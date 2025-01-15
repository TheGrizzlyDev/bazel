package net.starlark.java.eval;

import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.Opcodes;

import static org.objectweb.asm.Opcodes.ACC_PUBLIC;
import static org.objectweb.asm.Opcodes.ACONST_NULL;
import static org.objectweb.asm.Opcodes.ALOAD;
import static org.objectweb.asm.Opcodes.ARETURN;
import static org.objectweb.asm.Opcodes.INVOKESPECIAL;
import static org.objectweb.asm.Opcodes.RETURN;
import static org.objectweb.asm.Opcodes.V17;

final class Jit {
  public static Class<?> compile(StarlarkFunction fn) throws ClassNotFoundException {
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
    constructorVisitor.visitMaxs(1, 1);
    constructorVisitor.visitEnd();

    var methodVisitor = cw.visitMethod(
        Opcodes.ACC_PUBLIC,
        "call",
        "(Lnet/starlark/java/eval/StarlarkThread$Frame;)Ljava/lang/Object;",
        null,
        null);

    methodVisitor.visitCode();

    methodVisitor.visitInsn(ACONST_NULL);
    methodVisitor.visitInsn(ARETURN);

    methodVisitor.visitMaxs(1, 1);
    methodVisitor.visitEnd();
//    methodVisitor.visitEnd();
//    fnImplWriter.visitEnd();

//    var statements = fn.rfn.getBody();
//    for (Statement statement : statements) {
//      switch (statement.kind()) {
//        case ASSIGNMENT -> {
//          visitAssignment()
//        }
//        default -> {
//          throw new RuntimeException(String.format("Missing statement: %s%n", statement));
//        }
//      }
//    }

    cw.visitEnd();

    var cl = new SingleClassLoader(Jit.class.getClassLoader(), className, cw.toByteArray());

    return cl.loadClass(className);
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
