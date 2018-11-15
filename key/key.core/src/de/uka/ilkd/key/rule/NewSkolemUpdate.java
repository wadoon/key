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

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.op.SchemaVariable;

/**
 * Variable condition used if a new skolem update is introduced.
 */
public class NewSkolemUpdate {
    private final SchemaVariable sv;

    public NewSkolemUpdate(SchemaVariable sv) {
        assert sv != null;
        this.sv = sv;
    }

    public SchemaVariable getSchemaVariable() {
        return sv;
    }

    @Override
    public String toString() {
        return String.format("\\new(\\update %s))", sv);
    }
}