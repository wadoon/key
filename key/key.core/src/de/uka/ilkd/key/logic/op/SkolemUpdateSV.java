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
 * Schema variable representing an update that is instantiated with fresh Skolem
 * constants.
 */
public final class SkolemUpdateSV extends AbstractSV {

    /**
     * Creates a new schema variable that is used as placeholder for skolem
     * updates.
     *
     * @param name
     *            the Name of the SchemaVariable
     */
    SkolemUpdateSV(Name name) {
        super(name, Sort.UPDATE, true, false);
    }

    @Override
    public String toString() {
        return toString("skolem update");
    }

    @Override
    public String proofToString() {
        return "\\schemaVar \\skolemUpdate " + name() + ";\n";
    }
}