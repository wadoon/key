// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package org.key_project.bytecode.core.logic.op;

import org.key_project.bytecode.core.bytecode.BytecodeSourceElement;
import org.key_project.bytecode.core.bytecode.BytecodeVisitor;
import org.key_project.bytecode.core.bytecode.abstraction.Type;
import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.op.CCProgramVariable;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.program.NameAbstractionTable;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
public abstract class ProgramVariable extends
        CCProgramVariable<BytecodeVisitor, BytecodeSourceElement> implements
        BytecodeSourceElement {

    private final boolean isFinal;
    private final boolean isStatic;

    /**
     * TODO: Document.
     *
     * @param name
     * @param s
     * @param t
     * @param isModel
     * @param isGhost
     */
    protected ProgramVariable(Name name, Sort s, Type t, boolean isModel,
            boolean isGhost) {
        this(name, s, t, isModel, isGhost, false, false);
    }

    /**
     * TODO: Document.
     *
     * @param name
     * @param s
     * @param t
     * @param isModel
     * @param isGhost
     */
    protected ProgramVariable(Name name, Sort s, Type t, boolean isModel,
            boolean isGhost, boolean isFinal, boolean isStatic) {
        super(name, s, t, isModel, isGhost);
        this.isFinal = isFinal;
        this.isStatic = isStatic;
    }

    /**
     * @return the isFinal
     */
    public boolean isFinal() {
        return isFinal;
    }

    /**
     * @return the isStatic
     */
    public boolean isStatic() {
        return isStatic;
    }
    
    @Override
    public Type getType() {
        // TODO Auto-generated method stub
        return (Type) super.getType();
    }

    // ---------------------------------------------------
    // Methods defined in SourceElement
    // ---------------------------------------------------

    @Override
    public void visit(BytecodeVisitor v) {
        v.performActionOnProgramVariable(this);
    }

    /**
     * equals modulo renaming is described in the corresponding comment in class
     * SourceElement. In this case two programvariables are considered to be
     * equal if they are assigned to the same abstract name or if they are the
     * same object.
     */
    @Override
    public boolean equalsModRenaming(BytecodeSourceElement se,
            NameAbstractionTable<BytecodeSourceElement> nat) {
        return nat.sameAbstractName(this, se);
    }

}
