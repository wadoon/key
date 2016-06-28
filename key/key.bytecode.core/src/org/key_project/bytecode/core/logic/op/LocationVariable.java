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

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.program.abstraction.SortedType;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class LocationVariable extends ProgramVariable {
    
    /**
     * TODO: Document.
     *
     * @param name
     * @param s
     * @param t
     * @param isModel
     * @param isGhost
     */
    public LocationVariable(Name name, SortedType t,
            boolean isModel, boolean isGhost, boolean isFinal, boolean isStatic) {
        super(name, t.getSort(), t, isModel, isGhost, isFinal, isStatic);
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
    public LocationVariable(Name name, SortedType t,
            boolean isModel, boolean isGhost) {
        super(name, t.getSort(), t, isModel, isGhost);
    }

    /**
     * TODO: Document.
     *
     * @param name
     * @param sortedType
     */
    public LocationVariable(Name name, SortedType t) {
        this(name, t, false, false);
    }

    @Override
    public Operator rename(Name name) {
        return new LocationVariable(name, getType(), isModel(), isGhost(), isFinal(), isStatic());
    }

}
