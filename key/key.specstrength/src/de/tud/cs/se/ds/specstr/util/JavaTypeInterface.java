// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.tud.cs.se.ds.specstr.util;

import java.util.List;
import java.util.stream.Collectors;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramMethod;

/**
 * An interface to the String designators for Java types.
 *
 * @author Dominic Steinhoefel
 */
public final class JavaTypeInterface {

    private JavaTypeInterface() {
        // Hidden utility class constructor
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

        final String fullName = type.getFullName();

        if (fullName.startsWith("[")) {
            // Array type name -- already correct
            // XXX I know this for primitives, what about object types?
            return fullName;
        }

        switch (fullName) {
        case "int":
            return "I";
        case "boolean":
            return "Z";
        case "char":
            return "C";
        case "long":
            return "LB";
        case "short":
            return "S";
        case "byte":
            return "B";
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
     * Returns a {@link String} describing the given {@link IProgramMethod}, of
     * the form:
     * <code>&lt;type&gt;#&lt;methodName&gt;&lt;methodTypeDescriptor&gt;</code>.
     *
     * @param m
     *            The {@link IProgramMethod} for which a descriptor should be
     *            generated.
     * @return A {@link String} describing the given {@link IProgramMethod}.
     */
    public static String getMethodDescriptor(IProgramMethod m) {
        return m.getContainerType().getFullName() + "::" + m.getName()
                + getMethodTypeDescriptor(m);
    }

}
