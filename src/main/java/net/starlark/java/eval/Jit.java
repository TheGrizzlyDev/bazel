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
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;

import static org.objectweb.asm.Opcodes.*;

final class Jit {
  private static final Type IMMUTABLE_MAP_TYPE = Type.getType(ImmutableMap.class);
  private static final Type OBJECT_TYPE = Type.getType(Object.class);
  private static final Type STARLARK_TYPE = Type.getType(Starlark.class);
  private static final Type ARRAY_LIST_TYPE = Type.getType(ArrayList.class);
  private static final Type HASH_MAP_TYPE = Type.getType(HashMap.class);
  private static final Type STARLARK_THREAD_TYPE = Type.getType(StarlarkThread.class);
  private static final Type STARLARK_FRAME_TYPE = Type.getType(StarlarkThread.Frame.class);
  private static final Type LIST_TYPE = Type.getType(List.class);
  private static final Type MAP_TYPE = Type.getType(Map.class);
  private static final Type INTEGER_TYPE = Type.getType(Integer.class);
  private static final Type EVAL_TYPE = Type.getType(Eval.class);
  private static final Type RESOLVER_FUNCTION_TYPE = Type.getType(Resolver.Function.class);
  private static final Type STARLARK_FUNCTION_TYPE = Type.getType(StarlarkFunction.class);
  private static final Type STARLARK_CALLABLE_TYPE = Type.getType(StarlarkCallable.class);
  private static final Type STARLARK_INT_TYPE = Type.getType(StarlarkInt.class);
  private static final Type ARRAY_OBJECT_TYPE = Type.getType(Object[].class);
  private static final Type STARLARK_ITERABLE_TYPE = Type.getType(StarlarkIterable.class);
  private static final Type ITERATOR_TYPE = Type.getType(Iterator.class);

  public static Function<StarlarkThread.Frame, Object> compile(StarlarkFunction fn) {
    var cw = new ClassWriter(ClassWriter.COMPUTE_MAXS | ClassWriter.COMPUTE_FRAMES);
    String className = String.format("JitImpl%s", fn.getName().replaceAll("\\W", ""));
    HashMap<Integer, Resolver.Function> resolvedFunctions = new HashMap<>();

    jitStarlarkFn(fn, cw, className, resolvedFunctions);

    var cl = new SingleClassLoader(Jit.class.getClassLoader(), className, cw.toByteArray());

    try {
      Class<?> jitClass = cl.loadClass(className);

      Constructor<?> constructor = jitClass.getConstructor();
      Object jitMethodInstance = constructor.newInstance();
      Method call = jitClass.getMethod("call", StarlarkThread.Frame.class, StarlarkThread.class, Map.class);

      return frame -> {
        try {
          return call.invoke(jitMethodInstance, frame, frame.thread, resolvedFunctions);
        } catch (IllegalAccessException | InvocationTargetException e) {
          throw new RuntimeException(e);
        }
      };
    } catch (ClassNotFoundException | NoSuchMethodException | InvocationTargetException | IllegalAccessException |
             InstantiationException e) {
      throw new RuntimeException(e);
    }
  }

  private static void jitStarlarkFn(StarlarkFunction fn, ClassWriter cw, String className, HashMap<Integer, Resolver.Function> resolvedFunctions) {
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
    constructorVisitor.visitMaxs(0, 0);
    constructorVisitor.visitEnd();

    var methodVisitor = cw.visitMethod(
        ACC_PUBLIC,
        "call",
        String.format(
            "(%s%s%s)%s",
            STARLARK_FRAME_TYPE.getDescriptor(),
            STARLARK_THREAD_TYPE.getDescriptor(),
            MAP_TYPE.getDescriptor(),
            OBJECT_TYPE.getDescriptor()
        ),
        null,
        null);
    methodVisitor.visitCode();

    var statements = fn.rfn.getBody();
    for (Statement statement : statements) {
      visitStatement(statement, methodVisitor, resolvedFunctions);
    }

    methodVisitor.visitInsn(ACONST_NULL);
    methodVisitor.visitInsn(ARETURN);
    methodVisitor.visitMaxs(0, 0);

    methodVisitor.visitEnd();
    cw.visitEnd();

    verifyClassWriter(cw);
  }

  private static void visitStatement(Statement statement, MethodVisitor methodVisitor, Map<Integer, Resolver.Function> resolvedFunctions) {
    switch (statement.kind()) {
      case RETURN -> {
        visitReturn(methodVisitor, (ReturnStatement) statement);
      }
      case EXPRESSION -> {
        visitExpression(methodVisitor, ((ExpressionStatement) statement).getExpression());
        methodVisitor.visitInsn(POP);
      }
      case DEF -> {
        visitDef(methodVisitor, (DefStatement) statement, resolvedFunctions);
      }
      case FOR -> {
        visitFor(methodVisitor, (ForStatement) statement, resolvedFunctions);
      }
      default -> {
        throw new IllegalStateException(String.format("Missing statement '%s': %s%n", statement.kind(), statement));
      }
    }
  }

  private static void visitFor(MethodVisitor methodVisitor, ForStatement statement, Map<Integer, Resolver.Function> resolvedFunctions) {
    visitExpression(methodVisitor, statement.getCollection());
    methodVisitor.visitMethodInsn(INVOKEINTERFACE, STARLARK_ITERABLE_TYPE.getInternalName(), "iterator", String.format("()%s", ITERATOR_TYPE.getDescriptor()), true);

    Label startLoopLabel = new Label();
    Label endLoopLabel = new Label();

    methodVisitor.visitLabel(startLoopLabel);
    methodVisitor.visitInsn(DUP);
    methodVisitor.visitMethodInsn(INVOKEINTERFACE, ITERATOR_TYPE.getInternalName(), "hasNext", String.format("()%s", Type.BOOLEAN_TYPE.getDescriptor()), true);

    methodVisitor.visitJumpInsn(IFEQ, endLoopLabel);

    methodVisitor.visitInsn(DUP);
    methodVisitor.visitMethodInsn(INVOKEINTERFACE, ITERATOR_TYPE.getInternalName(), "next", String.format("()%s", OBJECT_TYPE.getDescriptor()), true);

    visitForAssignment(methodVisitor, statement.getVars());

    for (Statement loopStatement : statement.getBody()) {
      visitStatement(loopStatement, methodVisitor, resolvedFunctions);
    }

    methodVisitor.visitJumpInsn(GOTO, startLoopLabel);
    methodVisitor.visitLabel(endLoopLabel);
    methodVisitor.visitInsn(POP);
  }

  private static void visitForAssignment(MethodVisitor methodVisitor, Expression vars) {
    switch (vars.kind()) {
      case IDENTIFIER -> visitAssignToIdentifier(methodVisitor, (Identifier) vars);
      default -> throw new IllegalStateException("Unexpected value: " + vars.kind());
    }
  }

  private static void visitDef(MethodVisitor methodVisitor, DefStatement statement, Map<Integer, Resolver.Function> resolvedFunctions) {
    Resolver.Function resolvedFunction = statement.getResolvedFunction();

    if (resolvedFunction == null) {
      throw new IllegalArgumentException("we cannot handle a missing resolved function here yet");
    }

    resolvedFunctions.put(resolvedFunction.hashCode(), resolvedFunction);

    // push frame onto the stack
    methodVisitor.visitVarInsn(ALOAD, 1);

    // push resolvedFn map onto the stack
    methodVisitor.visitVarInsn(ALOAD, 3);

    // push fn hashcode onto the stack
    methodVisitor.visitLdcInsn(resolvedFunction.hashCode());
    methodVisitor.visitMethodInsn(INVOKESTATIC, INTEGER_TYPE.getInternalName(), "valueOf", String.format("(%s)%s", Type.INT_TYPE.getDescriptor(), INTEGER_TYPE.getDescriptor()), false);

    methodVisitor.visitMethodInsn(
        INVOKEINTERFACE,
        MAP_TYPE.getInternalName(),
        "get",
        String.format("(%s)%s", OBJECT_TYPE.getDescriptor(), OBJECT_TYPE.getDescriptor()),
        true
    );

    methodVisitor.visitTypeInsn(CHECKCAST, RESOLVER_FUNCTION_TYPE.getInternalName());

    // call public static StarlarkFunction Eval.newFunction(StarlarkThread.Frame fr, Resolver.Function rfn)
    methodVisitor.visitMethodInsn(INVOKESTATIC, EVAL_TYPE.getInternalName(), "newFunction", String.format("(%s%s)%s", STARLARK_FRAME_TYPE.getDescriptor(), RESOLVER_FUNCTION_TYPE.getDescriptor(), STARLARK_FUNCTION_TYPE.getDescriptor()), false);

    visitAssignToIdentifier(methodVisitor, statement.getIdentifier());
  }

  private static void visitAssignToIdentifier(MethodVisitor methodVisitor, Identifier identifier) {
    switch (identifier.getBinding().getScope()) {
      case GLOBAL -> {
        // push frame onto the stack
        methodVisitor.visitVarInsn(ALOAD, 1);
        // get function
        methodVisitor.visitMethodInsn(INVOKEVIRTUAL, STARLARK_FRAME_TYPE.getInternalName(), "getFunction", String.format("()%s", STARLARK_CALLABLE_TYPE.getDescriptor()), false);
        methodVisitor.visitTypeInsn(CHECKCAST, STARLARK_FUNCTION_TYPE.getInternalName());
        // swap with the value to assign
        methodVisitor.visitInsn(SWAP);
        methodVisitor.visitLdcInsn(identifier.getBinding().getIndex());
        methodVisitor.visitInsn(SWAP);

        // void StarlarkFunction.setGlobal(int progIndex, Object value)
        methodVisitor.visitMethodInsn(INVOKEVIRTUAL, STARLARK_FUNCTION_TYPE.getInternalName(), "setGlobal", String.format("(%s%s)%s", Type.INT_TYPE.getDescriptor(), OBJECT_TYPE.getDescriptor(), Type.VOID_TYPE.getDescriptor()), false);
      }
      case LOCAL -> {
        // push frame onto the stack
        methodVisitor.visitVarInsn(ALOAD, 1);

        // get locals onto the stack
        methodVisitor.visitFieldInsn(GETFIELD, STARLARK_FRAME_TYPE.getInternalName(), "locals", ARRAY_OBJECT_TYPE.getInternalName());

        // swap locals with value to assign
        methodVisitor.visitInsn(SWAP);

        // push index of identifier in locals array
        methodVisitor.visitLdcInsn(identifier.getBinding().getIndex());

        // swap index and value
        methodVisitor.visitInsn(SWAP);

        // assign to array
        methodVisitor.visitInsn(AASTORE);
      }
      default -> throw new IllegalStateException("Unexpected value: " + identifier.getBinding().getScope());
    }
  }

  private static void visitReturn(MethodVisitor methodVisitor, ReturnStatement statement) {
    Expression result = statement.getResult();
    if (result == null) {
      methodVisitor.visitInsn(ACONST_NULL);
    } else {
      visitExpression(methodVisitor, result);
    }
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
    switch (exp.getValue()) {
      case Integer ignored -> {
        visitStarlarkIntBoxing(methodVisitor);
      }
      default -> throw new IllegalStateException("Unexpected value: " + exp.getValue());
    }
  }

  private static void visitBinaryOperator(MethodVisitor methodVisitor, BinaryOperatorExpression exp) {
    visitExpression(methodVisitor, exp.getX());
    visitExpression(methodVisitor, exp.getY());
    switch (exp.getOperator()) {
      case PLUS -> visitSumOperator(methodVisitor);
      default -> throw new IllegalStateException("Unexpected value: " + exp.getOperator());
    }
  }

  private static void visitSumOperator(MethodVisitor methodVisitor) {
    methodVisitor.visitMethodInsn(INVOKESTATIC, STARLARK_INT_TYPE.getInternalName(), "add", String.format("(%s%s)%s", STARLARK_INT_TYPE.getDescriptor(), STARLARK_INT_TYPE.getDescriptor(), STARLARK_INT_TYPE.getDescriptor()), false);
  }

  private static void visitStringLiteral(MethodVisitor methodVisitor, StringLiteral exp) {
    methodVisitor.visitLdcInsn(exp.getValue());
  }

  private static void visitIdentifier(MethodVisitor methodVisitor, Identifier exp) {
    var binding = exp.getBinding();
    switch (Objects.requireNonNull(binding).getScope()) {
      case UNIVERSAL -> {
        methodVisitor.visitFieldInsn(GETSTATIC, STARLARK_TYPE.getInternalName(), "UNIVERSE", IMMUTABLE_MAP_TYPE.getDescriptor());
        methodVisitor.visitLdcInsn(binding.getName());

        // replace with Map.get
        methodVisitor.visitMethodInsn(INVOKEVIRTUAL, IMMUTABLE_MAP_TYPE.getInternalName(), "get", String.format("(%s)%s", OBJECT_TYPE.getDescriptor(), OBJECT_TYPE.getDescriptor()), false);
      }
      case GLOBAL -> {

        // push frame onto the stack
        methodVisitor.visitVarInsn(ALOAD, 1);
        // get function
        methodVisitor.visitMethodInsn(INVOKEVIRTUAL, STARLARK_FRAME_TYPE.getInternalName(), "getFunction", String.format("()%s", STARLARK_CALLABLE_TYPE.getDescriptor()), false);
        methodVisitor.visitTypeInsn(CHECKCAST, STARLARK_FUNCTION_TYPE.getInternalName());

        methodVisitor.visitLdcInsn(exp.getBinding().getIndex());

        // Object StarlarkFunction.getGlobal(int progIndex)
        methodVisitor.visitMethodInsn(INVOKEVIRTUAL, STARLARK_FUNCTION_TYPE.getInternalName(), "getGlobal", String.format("(%s)%s", Type.INT_TYPE.getDescriptor(), OBJECT_TYPE.getDescriptor()), false);
      }
      case LOCAL -> {
        // push frame onto the stack
        methodVisitor.visitVarInsn(ALOAD, 1);

        // get locals onto the stack
        methodVisitor.visitFieldInsn(GETFIELD, STARLARK_FRAME_TYPE.getInternalName(), "locals", ARRAY_OBJECT_TYPE.getInternalName());

        // push index of identifier in locals array
        methodVisitor.visitLdcInsn(binding.getIndex());

        // swap index and value
        methodVisitor.visitInsn(AALOAD);
      }
      default -> throw new IllegalStateException("Unexpected value: " + binding.getScope());
    }
  }

  private static void visitCall(MethodVisitor methodVisitor, CallExpression exp) {

    // Object Starlark.call(StarlarkThread thread, Object fn, List<Object> args, Map<String, Object> kwargs)
    // push StarlarkThread onto the stack
    methodVisitor.visitVarInsn(ALOAD, 2);
    // push fn onto the stack
    visitExpression(methodVisitor, exp.getFunction());

    methodVisitor.visitTypeInsn(NEW, ARRAY_LIST_TYPE.getInternalName());
    methodVisitor.visitInsn(DUP);
    methodVisitor.visitMethodInsn(INVOKESPECIAL, ARRAY_LIST_TYPE.getInternalName(), "<init>", "()V", false);

    for (Argument argument : exp.getArguments()) {
      switch (argument) {
        case Argument.Positional pos -> {
          methodVisitor.visitInsn(DUP);
          visitExpression(methodVisitor, pos.getValue());
          methodVisitor.visitMethodInsn(INVOKEVIRTUAL, ARRAY_LIST_TYPE.getInternalName(), "add", String.format("(%s)%s", OBJECT_TYPE.getDescriptor(), Type.BOOLEAN_TYPE.getDescriptor()), false);
          methodVisitor.visitInsn(POP); // ignore index of value added
        }
        default -> throw new IllegalStateException("Unexpected value: " + argument);
      }
    }

    methodVisitor.visitTypeInsn(NEW, HASH_MAP_TYPE.getInternalName());
    methodVisitor.visitInsn(DUP);
    methodVisitor.visitMethodInsn(INVOKESPECIAL, HASH_MAP_TYPE.getInternalName(), "<init>", "()V", false);

    methodVisitor.visitMethodInsn(
        INVOKESTATIC,
        STARLARK_TYPE.getInternalName(),
        "call",
        String.format(
            "(%s%s%s%s)%s",
            STARLARK_THREAD_TYPE.getDescriptor(),
            OBJECT_TYPE.getDescriptor(),
            LIST_TYPE.getDescriptor(),
            MAP_TYPE.getDescriptor(),
            OBJECT_TYPE.getDescriptor()
        ),
        false);
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

  private static void visitStarlarkIntBoxing(MethodVisitor methodVisitor) {
    methodVisitor.visitMethodInsn(INVOKESTATIC, STARLARK_INT_TYPE.getInternalName(), "of", String.format("(%s)%s", Type.INT_TYPE.getDescriptor(), STARLARK_INT_TYPE.getDescriptor()), false);
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
//
//  public static final class RuntimeUtils {
//    public static Object sum(Object x, Object y) {
//      if (x instanceof Integer xInt && y instanceof Integer yInt) {
//        return xInt + yInt;
//      }
//      throw new IllegalArgumentException(String.format("Cannot sum types '%s' and '%s'", x.getClass().getName(), y.getClass().getName()));
//    }
//  }
}
