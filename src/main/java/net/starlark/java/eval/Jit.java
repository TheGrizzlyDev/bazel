package net.starlark.java.eval;

import com.google.common.collect.ImmutableMap;
import net.starlark.java.syntax.*;
import org.objectweb.asm.*;
import org.objectweb.asm.util.CheckClassAdapter;

import java.io.PrintWriter;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.Consumer;
import java.util.function.Function;

import static org.objectweb.asm.Opcodes.*;

final class Jit {
  public enum RuntimeType {
    INT,
    LONG,
    FLOAT,
    DOUBLE,
    OBJ
  }

  public static Function<StarlarkThread.Frame, Object> compile(StarlarkFunction fn) {
    var cw = new ClassWriter(ClassWriter.COMPUTE_FRAMES);

    String className = String.format("JitImpl%s", fn.getName().replaceAll("\\W", ""));
    cw.visit(V17, ACC_PUBLIC, className, null, "java/lang/Object", null);

    var constructorVisitor = cw.visitMethod(
        ACC_PUBLIC, // Access flag for public
        "<init>",   // Constructor name
        "()V",      // Descriptor for a method with no arguments and void return type
        null,
        null
    );

    constructorVisitor.visitCode();
    constructorVisitor.visitVarInsn(ALOAD, 0);
    constructorVisitor.visitMethodInsn(INVOKESPECIAL, "java/lang/Object", "<init>", "()V", false);
    constructorVisitor.visitInsn(RETURN);
    constructorVisitor.visitMaxs(-1, -1);
    constructorVisitor.visitEnd();

    var methodVisitor = cw.visitMethod(
        ACC_PUBLIC,
        "call",
        "(Lnet/starlark/java/eval/StarlarkThread$Frame;Lnet/starlark/java/eval/StarlarkThread;)Ljava/lang/Object;",
        null,
        null);
    methodVisitor.visitCode();

    var statements = fn.rfn.getBody();
    for (Statement statement : statements) {
      switch (statement.kind()) {
        case RETURN -> {
          visitReturn(methodVisitor, ((ReturnStatement) statement));
        }
        default -> {
          throw new IllegalStateException(String.format("Missing statement '%s': %s%n", statement.kind(), statement));
        }
      }
    }

    methodVisitor.visitMaxs(-1, -1);

    methodVisitor.visitEnd();
    cw.visitEnd();

    verifyClassWriter(cw);

    var cl = new SingleClassLoader(Jit.class.getClassLoader(), className, cw.toByteArray());

    try {
      Class<?> jitClass = cl.loadClass(className);

      Constructor<?> constructor = jitClass.getConstructor();
      Object jitMethodInstance = constructor.newInstance();
      Method call = jitClass.getMethod("call", StarlarkThread.Frame.class, StarlarkThread.class);

      return frame -> {
        try {
          return call.invoke(jitMethodInstance, frame, frame.thread);
        } catch (IllegalAccessException | InvocationTargetException e) {
          throw new RuntimeException(e);
        }
      };
    } catch (ClassNotFoundException | NoSuchMethodException | InvocationTargetException | IllegalAccessException |
             InstantiationException e) {
      throw new RuntimeException(e);
    }
  }

  private static void visitReturn(MethodVisitor methodVisitor, ReturnStatement statement) {
    visitExpression(methodVisitor, statement.getResult());
    methodVisitor.visitInsn(ARETURN);
  }

  private static void visitExpression(MethodVisitor methodVisitor, Expression exp) {
    switch (exp.kind()) {
      case CALL -> visitCall(methodVisitor, (CallExpression) exp);
      case IDENTIFIER -> visitIdentifier(methodVisitor, (Identifier) exp);
      case STRING_LITERAL -> visitStringLiteral(methodVisitor, (StringLiteral) exp);
      case BINARY_OPERATOR -> visitBinaryOperator(methodVisitor, (BinaryOperatorExpression) exp);
      case INT_LITERAL -> visitIntLiteral(methodVisitor, (IntLiteral) exp);
      default -> throw new IllegalStateException("Unexpected value: " + exp.kind());
    }
  }

  private static void visitIntLiteral(MethodVisitor methodVisitor, IntLiteral exp) {
    methodVisitor.visitLdcInsn(exp.getValue());
    visitRuntimeType(methodVisitor, exp.getValue());
  }

  private static void visitBinaryOperator(MethodVisitor methodVisitor, BinaryOperatorExpression exp) {
    visitExpression(methodVisitor, exp.getX());
    visitExpression(methodVisitor, exp.getY());
    switch (exp.getOperator()) {
      case PLUS -> visitSumOperator(methodVisitor, exp);
      default -> throw new IllegalStateException("Unexpected value: " + exp.getOperator());
    }
  }

  private static void visitSumOperator(MethodVisitor methodVisitor, BinaryOperatorExpression exp) {
    // TODO this should change sum based on types
    methodVisitor.visitInsn(POP); // hack: consume Y type
    methodVisitor.visitInsn(SWAP); // hack: swap operand Y value with X type
    methodVisitor.visitInsn(POP); // hack: consume X type
    methodVisitor.visitInsn(IADD);
    methodVisitor.visitLdcInsn(RuntimeType.INT.ordinal());
  }

  private static void visitStringLiteral(MethodVisitor methodVisitor, StringLiteral exp) {
    methodVisitor.visitLdcInsn(exp.getValue());
  }

  private static void visitIdentifier(MethodVisitor methodVisitor, Identifier exp) {
    Type immutableMapType = Type.getType(ImmutableMap.class);
    Type objectType = Type.getType(Object.class);
    var binding = exp.getBinding();
    switch (Objects.requireNonNull(binding).getScope()) {
      case UNIVERSAL -> {
        Type starlarkType = Type.getType(Starlark.class);
        methodVisitor.visitFieldInsn(GETSTATIC, starlarkType.getInternalName(), "UNIVERSE", immutableMapType.getDescriptor());
        methodVisitor.visitLdcInsn(binding.getName());
        methodVisitor.visitMethodInsn(INVOKEVIRTUAL, immutableMapType.getInternalName(), "get", String.format("(%s)%s", objectType.getDescriptor(), objectType.getDescriptor()), false);
      }
      default -> throw new IllegalStateException("Unexpected value: " + binding.getScope());
    }
  }

  private static void visitCall(MethodVisitor methodVisitor, CallExpression exp) {
    Type starlarkType = Type.getType(Starlark.class);
    Type arrayListType = Type.getType(ArrayList.class);
    Type hashMapType = Type.getType(HashMap.class);
    Type objectType = Type.getType(Object.class);

    // Object Starlark.call(StarlarkThread thread, Object fn, List<Object> args, Map<String, Object> kwargs)
    // push StarlarkThread onto the stack
    methodVisitor.visitVarInsn(ALOAD, 2);
    // push fn onto the stack
    visitExpression(methodVisitor, exp.getFunction());

    methodVisitor.visitTypeInsn(NEW, arrayListType.getInternalName());
    methodVisitor.visitInsn(DUP);
    methodVisitor.visitMethodInsn(INVOKESPECIAL, arrayListType.getInternalName(), "<init>", "()V", false);

    for (Argument argument : exp.getArguments()) {
      switch (argument) {
        case Argument.Positional pos -> {
          methodVisitor.visitInsn(DUP);
          visitExpression(methodVisitor, pos.getValue());
          visitAutoboxing(methodVisitor);
          methodVisitor.visitMethodInsn(INVOKEVIRTUAL, arrayListType.getInternalName(), "add", String.format("(%s)%s", objectType.getDescriptor(), Type.BOOLEAN_TYPE.getDescriptor()), false);
          methodVisitor.visitInsn(POP);
        }
        default -> throw new IllegalStateException("Unexpected value: " + argument);
      }
    }

    methodVisitor.visitTypeInsn(NEW, hashMapType.getInternalName());
    methodVisitor.visitInsn(DUP);
    methodVisitor.visitMethodInsn(INVOKESPECIAL, hashMapType.getInternalName(), "<init>", "()V", false);

    methodVisitor.visitMethodInsn(
        INVOKESTATIC,
        starlarkType.getInternalName(),
        "call",
        String.format(
            "(%s%s%s%s)%s",
            Type.getType(StarlarkThread.class).getDescriptor(),
            Type.getType(Object.class).getDescriptor(),
            Type.getType(List.class).getDescriptor(),
            Type.getType(Map.class).getDescriptor(),
            Type.getType(Object.class).getDescriptor()
        ),
        false);
  }

  private static void visitRuntimeType(MethodVisitor methodVisitor, Object target) {
    switch (target) {
      case Integer ignored -> {
        methodVisitor.visitLdcInsn(RuntimeType.INT.ordinal());
      }
      default -> throw new IllegalStateException("Unexpected value: " + target);
    }
  }

  private static void visitAutoboxing(MethodVisitor methodVisitor) {
    Type integerType = Type.getType(Integer.class);
    methodVisitor.visitInsn(POP);
    methodVisitor.visitMethodInsn(INVOKESTATIC, integerType.getInternalName(), "valueOf", String.format("(%s)%s", Type.INT_TYPE.getDescriptor(), integerType.getDescriptor()));
  }

  private static void verifyClassWriter(ClassWriter cw) {
    PrintWriter pw = new PrintWriter(System.out);
    CheckClassAdapter.verify(new ClassReader(cw.toByteArray()), true, pw);
  }

  private static void visitPrintLastElementOnStack(MethodVisitor methodVisitor) {
    methodVisitor.visitInsn(DUP); // Duplicate the top element of the stack
    methodVisitor.visitMethodInsn(
        INVOKESTATIC,
        "java/lang/String",
        "valueOf",
        "(Ljava/lang/Object;)Ljava/lang/String;",
        false
    );
    methodVisitor.visitFieldInsn(
        GETSTATIC,
        "java/lang/System",
        "out",
        "Ljava/io/PrintStream;"
    );
    methodVisitor.visitInsn(SWAP);
    methodVisitor.visitMethodInsn(
        INVOKEVIRTUAL,
        "java/io/PrintStream",
        "println",
        "(Ljava/lang/String;)V",
        false
    );
  }

  private static void visitPushClassNameOnStack(MethodVisitor methodVisitor) {
    methodVisitor.visitInsn(DUP); // Duplicate the last object on the stack
    methodVisitor.visitMethodInsn(
        INVOKEVIRTUAL,
        "java/lang/Object",
        "getClass",
        "()Ljava/lang/Class;",
        false
    );
    methodVisitor.visitMethodInsn(
        INVOKEVIRTUAL,
        "java/lang/Class",
        "getName",
        "()Ljava/lang/String;",
        false
    );
  }

  private static final class SingleClassLoader extends ClassLoader {
    private final Class<?> clazz;
    private final String name;

    private SingleClassLoader(ClassLoader parent, String name, byte[] classBytes) {
      super(parent);
      this.name = name;
      this.clazz = defineClass(name, classBytes, 0, classBytes.length);
    }

    @Override
    public Class<?> loadClass(String name) throws ClassNotFoundException {
      if (this.name.equals(name))
        return clazz;
      return super.loadClass(name);
    }
  }
}
