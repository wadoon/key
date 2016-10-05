package de.tud.cs.se.ds.psec.util;

import java.util.List;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableArray;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;

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
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramMethod;

/**
 * Utility methods for extracting information about type, method and field
 * declarations.
 *
 * @author Dominic Scheurer
 */
public class InformationExtraction implements Opcodes {

    /**
     * Internally (in bytecode), fully qualified class names are spelled out
     * with slashes instead of dots as separators. This method converts normal
     * class names to these internal representations.
     *
     * @param javaClassName
     *            The class name to convert.
     * @return An internal representation of the class name.
     */
    public static String toInternalName(String javaClassName) {
        return javaClassName.replaceAll("\\.", "/");
    }

    /**
     * Internally (in bytecode), fully qualified class names are spelled out
     * with slashes instead of dots as separators. This method returns an
     * internal representation for the name of the supplied {@link KeYJavaType}.
     *
     * @param javaType
     *            The type to return an internal name for.
     * @return An internal representation of the class name of the given
     *         {@link KeYJavaType}.
     */
    public static String toInternalName(KeYJavaType javaType) {
        return toInternalName(javaType.getFullName());
    }

    /**
     * Returns all implemented interfaces for a given {@link TypeDeclaration}.
     * 
     * @param t
     *            The {@link TypeDeclaration} to return the implemented
     *            interfaces for.
     * @return The array of interface names for the {@link TypeDeclaration}. May
     *         be null if there is no implemented interface.
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
     * Returns the internal name of the super class of a
     * {@link TypeDeclaration}. The fallback is "java/lang/Object".
     * 
     * @param t
     *            The {@link TypeDeclaration} to return the internal name of the
     *            superclass for.
     * @return The super class of the given {@link TypeDeclaration} (defaults to
     *         "java/lang/Object").
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
     * Creates an ASM opcode for the given {@link TypeDeclaration}. An opcode
     * specifies the visibility and other characteristics, like whether the
     * {@link TypeDeclaration} is static.
     * 
     * @param classDecl
     *            The {@link TypeDeclaration} to create an ASM opcode for.
     * @return The generated ASM opcode corresponding to the given
     *         {@link TypeDeclaration}.
     */
    public static int createOpcode(TypeDeclaration classDecl) {
        return InformationExtraction.createOpcode(classDecl.isPublic(),
                classDecl.isProtected(), classDecl.isPrivate(),
                classDecl.isAbstract(), classDecl.isFinal(),
                classDecl.isStatic(), classDecl.isInterface());
    }

    /**
     * Creates an ASM opcode for the given {@link ProgramMethod}. An opcode
     * specifies the visibility and other characteristics, like whether the
     * {@link ProgramMethod} is static.
     *
     * @param methodDecl
     *            The {@link ProgramMethod} to create an ASM opcode for.
     * @return The generated ASM opcode corresponding to the given
     *         {@link ProgramMethod}.
     */
    public static int createOpcode(ProgramMethod methodDecl) {
        return InformationExtraction.createOpcode(methodDecl.isPublic(),
                methodDecl.isProtected(), methodDecl.isPrivate(),
                methodDecl.isAbstract(), methodDecl.isFinal(),
                methodDecl.isStatic(), false);
    }

    /**
     * Creates an ASM opcode for the given {@link FieldDeclaration}. An opcode
     * specifies the visibility and other characteristics, like whether the
     * {@link FieldDeclaration} is static.
     *
     * @param fieldDecl
     *            The {@link FieldDeclaration} to create an ASM opcode for.
     * @return The generated ASM opcode corresponding to the given
     *         {@link FieldDeclaration}.
     */
    public static int createOpcode(FieldDeclaration fieldDecl) {
        return createOpcode(fieldDecl.isPublic(), fieldDecl.isProtected(),
                fieldDecl.isPrivate(), false, fieldDecl.isFinal(),
                fieldDecl.isStatic(), false);
    }

    /**
     * Creates an ASM opcode for the given boolean characteristics.
     *
     * @param isPublic
     *            true iff the opcode should have the "public" flag.
     * @param isProtected
     *            true iff the opcode should have the "protected" flag.
     * @param isPrivate
     *            true iff the opcode should have the "private" flag.
     * @param isAbstract
     *            true iff the opcode should have the "abstract" flag.
     * @param isFinal
     *            true iff the opcode should have the "final" flag.
     * @param isStatic
     *            true iff the opcode should have the "static" flag.
     * @param isInterface
     *            true iff the opcode should have the "interface" flag.
     * @return An ASM opcode for the given boolean parameters.
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
     * Returns a bytecode type descriptor for a given {@link KeYJavaType}.
     * <p>
     * For instance, a descriptor for <code>de.tud.Test</code> would be
     * <code>Lde/tud/Test;</code>. For an int, it would be <code>I</code>.
     *
     * @param type
     *            The {@link KeYJavaType} to return a bytecode type descriptor
     *            for.
     * @return A bytecode type descriptor for the given {@link KeYJavaType}.
     * @see Type#getDescriptor(Class)
     */
    public static String typeToTypeDescriptor(KeYJavaType type) {
        if (type.equals(KeYJavaType.VOID_TYPE)) {
            return "V";
        }

        // 'V' - void
        // 'Z' - boolean
        // 'C' - char
        // 'B' - byte
        // 'S' - short
        // 'I' - int
        // 'F' - float (unsupported)
        // 'J' - long
        // 'D' - double (unsupported)

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
     * Computes a bytecode method type descriptor for the given
     * {@link ProgramMethod}. An example is <code>(ILjava/lang/Object;)Z</code>
     * for a method taking an int and an Object, and returning a boolean.
     *
     * @param m
     *            The {@link ProgramMethod} for the signature of which a method
     *            type descriptor should be created.
     * @return A method type descriptor describing the signature of the given
     *         {@link ProgramMethod}.
     */
    public static String getMethodTypeDescriptor(IProgramMethod m) {
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
     * Retrieves all {@link KeYJavaType}s declared in the given
     * {@link KeYEnvironment}.
     * 
     * @param environment
     *            The {@link KeYEnvironment} to retrieve all declared
     *            {@link KeYJavaType}s from.
     * @return A {@link List} of all declared {@link KeYJavaType}s in the given
     *         {@link KeYEnvironment}.
     */
    public static List<KeYJavaType> getDeclaredTypes(
            KeYEnvironment<DefaultUserInterfaceControl> environment) {
        // @formatter:off
        return environment.getJavaInfo().getAllKeYJavaTypes().parallelStream()
                .filter(t -> t.getJavaType() instanceof InterfaceDeclaration
                          || t.getJavaType() instanceof ClassDeclaration)
                .filter(t -> !((TypeDeclaration) t.getJavaType()).isLibraryClass())
                .collect(Collectors.toList());
        // @formatter:on
    }

}
