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

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * A "Skolem" Schema Variable, i.e. one that should always be instantiated
 * freshly.
 *
 * @author Dominic Steinhoefel
 */
public abstract class SkolemSV extends AbstractSV {
    /**
     * A {@link SchemaVariable} for which this {@link SkolemSV} should be
     * deterministically instantiated. That is, the first time, it's created
     * like a normal {@link SkolemSV}, but the second time you call this method
     * for the same freshForSV, the same instantiation is returned. Realizes a
     * kind of weak Skolemization.
     */
    private final SchemaVariable freshForSV;

    SkolemSV(Name name, Sort sort, boolean rigid, SchemaVariable freshForSV) {
        super(name, sort, rigid, false);
        this.freshForSV = freshForSV;
    }

    SkolemSV(Name name, Sort sort) {
        this(name, sort, true, null);
    }

    public SchemaVariable getFreshForSV() {
        return freshForSV;
    }
}
