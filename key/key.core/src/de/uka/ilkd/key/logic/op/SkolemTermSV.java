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

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Schema variable that is instantiated with fresh Skolem constants. At the
 * moment, such schema variables have to be accompanied by a "NewDependingOn"
 * varcond, although with the removal of the meta variable mechanism, this would
 * no longer really be necessary.
 */
public final class SkolemTermSV extends SkolemSV {

    /**
     * Creates a new schema variable that is used as placeholder for skolem
     * terms.
     *
     * @param name
     *            the Name of the SchemaVariable
     * @param sort
     *            the Sort of the SchemaVariable and the matched type allowed to
     *            match a list of program constructs
     */
    SkolemTermSV(Name name, Sort sort) {
        super(name, sort);
        assert sort != Sort.UPDATE;
    }

    /**
     * Creates a new schema variable that is used as placeholder for skolem
     * terms.
     *
     * @param name
     *            the Name of the SchemaVariable
     * @param sort
     *            the Sort of the SchemaVariable and the matched type allowed to
     *            match a list of program constructs
     * @param freshForSV
     *            A {@link SchemaVariable} for which this {@link SkolemSV}
     *            should be deterministically instantiated. That is, the first
     *            time, it's created like a normal {@link SkolemSV}, but the
     *            second time you call this method for the same freshForSV, the
     *            same instantiation is returned. Realizes a kind of weak
     *            Skolemization.
     */
    SkolemTermSV(Name name, Sort sort, SchemaVariable freshForSV) {
        super(name, sort, freshForSV);
        assert sort != Sort.UPDATE;
    }

    @Override
    public String toString() {
        return toString(sort().toString() + " skolem term");
    }

    @Override
    public String proofToString() {
        return String.format("\\schemaVar %s %s %s;", //
            sort() == Sort.FORMULA ? "\\skolemFormula" : "\\skolemTerm", //
            sort().name(), //
            name());
    }
}