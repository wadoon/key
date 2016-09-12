package de.tud.cs.se.ds.psec.util;

import static org.objectweb.asm.Opcodes.*;

import java.util.List;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.Extends;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.Implements;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.op.ProgramMethod;

/**
 * Utility methods for extracting information about type, method and field
 * declarations.
 *
 * @author Dominic Scheurer
 */
public class InformationExtraction {

    /**
     * TODO
     *
     * @param javaClassName
     * @return
     */
    public static String toInternalName(String javaClassName) {
        return javaClassName.replaceAll("\\.", "/");
    }

    /**
     * TODO
     * 
     * @param t
     * @return
     */
    public static String[] getImplementing(TypeDeclaration typeDecl) {
        if (!(typeDecl instanceof ClassDeclaration)) {
            return null;
        }

        ClassDeclaration classDecl = (ClassDeclaration) typeDecl;

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

    /**
     * TODO
     * 
     * @param classDecl
     * @return
     */
    public static int createOpcode(TypeDeclaration classDecl) {
        return InformationExtraction.createOpcode(classDecl.isPublic(),
                classDecl.isProtected(),
                classDecl.isPrivate(), classDecl.isAbstract(),
                classDecl.isFinal(), classDecl.isStatic(),
                classDecl.isInterface());
    }

    /**
     * TODO
     *
     * @param methodDecl
     * @return
     */
    public static int createOpcode(ProgramMethod methodDecl) {
        return InformationExtraction.createOpcode(methodDecl.isPublic(),
                methodDecl.isProtected(),
                methodDecl.isPrivate(), methodDecl.isAbstract(),
                methodDecl.isFinal(), methodDecl.isStatic(), false);
    }

    /**
     * TODO
     *
     * @param isPublic
     * @param isProtected
     * @param isPrivate
     * @param isAbstract
     * @param isFinal
     * @param isStatic
     *            TODO
     * @param isInterface
     * @return
     */
    public static int createOpcode(boolean isPublic, boolean isProtected,
            boolean isPrivate, boolean isAbstract, boolean isFinal,
            boolean isStatic, boolean isInterface) {
        int opcode = 0;

        if (isPublic) {
            opcode += ACC_PUBLIC;
        } else if (isProtected) {
            opcode += ACC_PROTECTED;
        } else if (isPrivate) {
            opcode += ACC_PRIVATE;
        }

        if (isAbstract) {
            opcode += ACC_ABSTRACT;
        }

        if (isFinal) {
            opcode += ACC_FINAL;
        }

        if (isStatic) {
            opcode += ACC_STATIC;
        }

        if (isInterface) {
            opcode += ACC_INTERFACE;
        }

        return opcode;
    }

    /**
     * TODO
     *
     * @param fieldDecl
     * @return
     */
    public static int createOpcode(FieldDeclaration fieldDecl) {
        return createOpcode(fieldDecl.isPublic(), fieldDecl.isProtected(),
                fieldDecl.isPrivate(), false, fieldDecl.isFinal(),
                fieldDecl.isStatic(), false);
    }

    /**
     * TODO
     * 
     * @param t
     * @return
     */
    public static String getExtending(TypeDeclaration classDecl) {
        Extends ext = classDecl instanceof InterfaceDeclaration
                ? ((InterfaceDeclaration) classDecl).getExtendedTypes()
                : ((ClassDeclaration) classDecl).getExtendedTypes();
        String extending;

        if (ext != null) {
            ImmutableArray<TypeReference> supertypes = ext.getSupertypes();
            extending = toInternalName(
                    supertypes.get(0).getKeYJavaType().getFullName());
        } else {
            extending = "java/lang/Object";
        }

        return extending;
    }

    /**
     * TODO
     *
     * @param type
     * @return
     */
    public static String typeToTypeDescriptor(KeYJavaType type) {
        if (type.equals(KeYJavaType.VOID_TYPE)) {
            return "V";
        }

        String fullName;
        switch (fullName = type.getFullName()) {
        case "int":
            return "I";
        case "boolean":
            return "Z";
        // TODO: short, long?
        default:
            return "L" + toInternalName(fullName) + ";";
        }
    }

    /**
     * TODO
     *
     * @param m
     * @return
     */
    public static String getMethodTypeDescriptor(ProgramMethod m) {
        StringBuilder sb = new StringBuilder();

        sb.append("(");
        // TODO varargs parameters
        m.getParameters().forEach(s -> sb.append(
                typeToTypeDescriptor(s.getTypeReference().getKeYJavaType())));
        sb.append(")");
        sb.append(typeToTypeDescriptor(m.getReturnType()));

        return sb.toString();
    }

    /**
     * TODO
     * @param environment TODO
     * @param environment
     * 
     * @return
     */
    public static List<KeYJavaType> getDeclaredTypes(KeYEnvironment<DefaultUserInterfaceControl> environment) {
        // @formatter:off
        return environment.getJavaInfo().getAllKeYJavaTypes().parallelStream()
                .filter(t -> t.getJavaType() instanceof InterfaceDeclaration
                          || t.getJavaType() instanceof ClassDeclaration)
                .filter(t -> !((TypeDeclaration) t.getJavaType()).isLibraryClass())
                .collect(Collectors.toList());
        // @formatter:on
    }

}
