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

package org.key_project.common.core.logic.op;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.program.CCSourceElement;
import org.key_project.common.core.program.abstraction.SortedType;

/**
 * Class representing a program variable. Program variables have a sorted type
 * and can be model or ghost.
 *
 * @author Dominic Scheurer
 */
public abstract class CCProgramVariable extends AbstractSortedOperator
        implements CCSourceElement {

    private final SortedType type;
    private final boolean isModel;
    private final boolean isGhost;

    protected CCProgramVariable(Name name,
            Sort s,
            SortedType t,
            boolean isModel,
            boolean isGhost) {
        super(name, s == null ? t.getSort() : s, false);
        this.type = t;
        this.isModel = isModel;
        this.isGhost = isGhost;
        assert !(isModel && isGhost) : "A Program variable cannot both be model and ghost";

        assert sort() != Sort.FORMULA;
        assert sort() != Sort.UPDATE;
    }

    // ---------------------------------------------------
    // Own public interface
    // ---------------------------------------------------

    /**
     * Returns an equivalent variable with the new name.
     * 
     * @param name
     *            the new name
     * @return equivalent operator with the new name
     */
    abstract public Operator rename(Name name);

    /**
     * returns true iff the program variable has been declared as model
     */
    public boolean isModel() {
        return isModel;
    }

    /**
     * returns true if the program variable has been declared as ghost
     */
    public boolean isGhost() {
        return isGhost;
    }

    public boolean isImplicit() {
        return name().toString().startsWith("<");
    }

    public SortedType getType() {
        return type;
    }
}
