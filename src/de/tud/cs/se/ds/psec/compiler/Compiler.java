package de.tud.cs.se.ds.psec.compiler;

import static org.objectweb.asm.Opcodes.*;

import java.io.File;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import org.key_project.util.collection.ImmutableArray;
import org.objectweb.asm.AnnotationVisitor;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.FieldVisitor;
import org.objectweb.asm.MethodVisitor;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.Extends;
import de.uka.ilkd.key.java.declaration.Implements;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;

/**
 * TODO
 *
 * @author Dominic Scheurer
 */
public class Compiler {
    private static final int CLASS_VERSION = 52;
    private KeYEnvironment<DefaultUserInterfaceControl> environment;

    /**
     * TODO
     * 
     * @param javaFile
     * @throws ProblemLoaderException
     */
    public Compiler(File javaFile) throws ProblemLoaderException {
        environment = KeYEnvironment.load(
                SymbolicExecutionJavaProfile.getDefaultInstance(), javaFile,
                null, null, null, true);
    }

    /**
     * TODO
     * 
     * @return
     */
    public List<JavaTypeCompilationResult> compile() {
        // getDeclaredTypes().forEach(
        // t -> getProgramMethods(t).forEach(m -> environment.getServices()
        // .getSpecificationRepository().getContracts(t, m)
        // .forEach(c -> System.out.println(c.createProofObl(
        // environment.getInitConfig())))));

        List<KeYJavaType> declaredTypes = getDeclaredTypes();

        assert declaredTypes
                .size() > 0 : "Unexpectedly, no type is declared in the supplied Java file.";

        return toStream(declaredTypes).map(t -> compile(t.getJavaType()))
                .collect(Collectors.toList());
    }

    private JavaTypeCompilationResult compile(Type typeDecl) {
        if (typeDecl instanceof ClassDeclaration) {
            return compile((ClassDeclaration) typeDecl);
        }
        else if (typeDecl instanceof InterfaceDeclaration) {
            return compile((InterfaceDeclaration) typeDecl);
        }
        else {
            throw new UnsupportedOperationException(
                    "Unexpected top level type: " + typeDecl.getFullName());
        }
    }

    /**
     * TODO
     * 
     * @param t
     * @return
     */
    private JavaTypeCompilationResult compile(ClassDeclaration classDecl) {
        ClassWriter cw = new ClassWriter(
                ClassWriter.COMPUTE_MAXS + ClassWriter.COMPUTE_FRAMES);
        FieldVisitor fv;
        MethodVisitor mv;
        AnnotationVisitor av0;

        String extending = getExtending(classDecl);
        String[] implementing = getImplementing(classDecl);
        String internalName = toInternalName(classDecl.getFullName());

        cw.visit(CLASS_VERSION, createClassOpcode(classDecl), internalName,
                null, extending, implementing);

        cw.visitEnd();

        return new JavaTypeCompilationResult(cw.toByteArray(), internalName);
    }

    /**
     * TODO
     * 
     * @param t
     * @return
     */
    private JavaTypeCompilationResult compile(InterfaceDeclaration ifDecl) {
        //TODO: Probably it's possible to unify this with #comile(ClassDeclaration)
        
        ClassWriter cw = new ClassWriter(
                ClassWriter.COMPUTE_MAXS + ClassWriter.COMPUTE_FRAMES);
        FieldVisitor fv;
        MethodVisitor mv;
        AnnotationVisitor av0;

        String extending = getExtending(ifDecl);
        String internalName = toInternalName(ifDecl.getFullName());

        cw.visit(CLASS_VERSION, createClassOpcode(ifDecl) + ACC_INTERFACE, internalName, null,
                extending, null);

        cw.visitEnd();

        return new JavaTypeCompilationResult(cw.toByteArray(), internalName);
    }

    /**
     * TODO
     * 
     * @param t
     * @return
     */
    private String getExtending(TypeDeclaration classDecl) {
        Extends ext = classDecl instanceof InterfaceDeclaration
                ? ((InterfaceDeclaration) classDecl).getExtendedTypes()
                : ((ClassDeclaration) classDecl).getExtendedTypes();
        String extending;

        if (ext != null) {
            ImmutableArray<TypeReference> supertypes = ext.getSupertypes();
            extending = toInternalName(
                    supertypes.get(0).getKeYJavaType().getFullName());
        }
        else {
            extending = "java/lang/Object";
        }

        return extending;
    }

    /**
     * TODO
     * 
     * @param t
     * @return
     */
    private String[] getImplementing(ClassDeclaration classDecl) {
        Implements impl = classDecl.getImplementedTypes();
        String[] implementing = null;

        if (impl != null) {
            ImmutableArray<TypeReference> supertypes = impl.getSupertypes();
            implementing = new String[supertypes.size()];

            for (int i = 0; i < supertypes.size(); i++) {
                implementing[i] = toInternalName(
                        supertypes.get(i).getKeYJavaType().getFullName());
            }
        }

        return implementing;
    }

    private String toInternalName(String javaClassName) {
        return javaClassName.replaceAll("\\.", "/");
    }

    /**
     * TODO
     * 
     * @param classDecl
     * @return
     */
    private int createClassOpcode(TypeDeclaration classDecl) {
        int opcode = 0;

        if (classDecl.isPublic()) {
            opcode += ACC_PUBLIC;
        }
        else if (classDecl.isProtected()) {
            opcode += ACC_PROTECTED;
        }
        else if (classDecl.isPrivate()) {
            opcode += ACC_PRIVATE;
        }

        if (classDecl.isAbstract()) {
            opcode += ACC_ABSTRACT;
        }

        if (classDecl.isFinal()) {
            opcode += ACC_FINAL;
        }

        return opcode;
    }

    /**
     * TODO
     * 
     * @param environment
     * @return
     */
    private List<KeYJavaType> getDeclaredTypes() {
        // @formatter:off
        return environment.getJavaInfo().getAllKeYJavaTypes().parallelStream()
                .filter(t -> t.getJavaType() instanceof InterfaceDeclaration
                          || t.getJavaType() instanceof ClassDeclaration)
                .filter(t -> !((TypeDeclaration) t.getJavaType()).isLibraryClass())
                .collect(Collectors.toList());
        // @formatter:on
    }

    /**
     * TODO
     * 
     * @param t
     * @return
     */
    private List<IProgramMethod> getProgramMethods(KeYJavaType t) {
        return toStream(environment.getServices().getSpecificationRepository()
                .getContractTargets(t))
                        .filter(m -> (m instanceof IProgramMethod))
                        .map(m -> (IProgramMethod) m)
                        .collect(Collectors.toList());
    }

    /**
     * TODO
     * 
     * @param it
     * @return
     */
    private static <T> Stream<T> toStream(Iterable<T> it) {
        return StreamSupport.stream(it.spliterator(), false);
    }
}
