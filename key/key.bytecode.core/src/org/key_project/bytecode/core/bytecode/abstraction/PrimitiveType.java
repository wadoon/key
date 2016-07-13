// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package org.key_project.bytecode.core.bytecode.abstraction;

import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.bytecode.core.bytecode.IntOperandValue;
import org.key_project.bytecode.core.bytecode.OperandValue;
import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.theories.CCIntegerTheory;

/**
 * A program model element representing primitive types.
 * 
 * @author Dominic Scheurer
 */
public class PrimitiveType implements Type {

    // TODO: Implement this class, take corresponding Java class as orientation.
    // Probably also have to supply a OperandValue class for default values.

    // must be first in file.
    private static final Map<String, PrimitiveType> TYPE_MAP =
            new LinkedHashMap<String, PrimitiveType>();

    // must be first in file.
    private static final Map<Name, PrimitiveType> THEORY_MAP =
            new LinkedHashMap<Name, PrimitiveType>();

    public static PrimitiveType getPrimitiveType(String name) {
        return TYPE_MAP.get(name);
    }

    public static PrimitiveType getPrimitiveTypeByLDT(Name ldtName) {
        return THEORY_MAP.get(ldtName);
    }
    
    public static final PrimitiveType JAVA_INT =
            new PrimitiveType("int", new IntOperandValue(0), CCIntegerTheory.NAME);

    private final Name name;
    private final OperandValue defaultValue;
    private final Name theoryName;

    private PrimitiveType(String name, OperandValue defaultValue, Name theoryName) {
        this.defaultValue = defaultValue;
        this.name = new Name(name.intern());
        this.theoryName = theoryName;
        TYPE_MAP.put(name, this);

        if (theoryName != null) {
            THEORY_MAP.put(theoryName, this);
        }
    }

    @Override
    public boolean equals(Object o) {
        if (o instanceof PrimitiveType &&
                ((PrimitiveType) o).name().equals(name)) {
            return true;
        }
        return false;
    }

    @Override
    public int hashCode() {
        return name().toString().hashCode();
    }

    /**
     * returns the default value of the given type according to JLS ???4.5.5
     * <em>ATTENTION:</em> usually for byte and short this should be (byte) 0
     * (rsp. (short)0) but currently is just 0.
     * 
     * @return the default value of the given type according to JLS ???4.5.5
     */
    @Override
    public OperandValue defaultValue() {
        return defaultValue;
    }

    /**
     * Returns the name of type.
     * 
     * @return the full name of this program model element.
     */
    @Override
    public String toString() {
        return name.toString();
    }

    /**
     * Returns whether this is a Java type which translates to int in DL.
     */
    public boolean isIntegerType() {
        return true; //TODO
//        return this == JAVA_BYTE
//                || this == JAVA_CHAR
//                || this == JAVA_SHORT
//                || this == JAVA_INT
//                || this == JAVA_LONG
//                || this == JAVA_BIGINT;
    }

    /**
     * Gets the name of the LDT corresponding to this primitive type.
     *
     * @return may be null if no name set
     */
    public Name getCorrespondingTheoryName() {
        return theoryName;
    }

    @Override
    public Sort getSort() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Name name() {
        return name;
    }
}
