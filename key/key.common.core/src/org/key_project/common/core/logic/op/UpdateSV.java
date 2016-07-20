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

package org.key_project.common.core.logic.op;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.sort.Sort;

/**
 * A schema variable that is used as placeholder for updates.
 */
public final class UpdateSV extends AbstractSV {

    public UpdateSV(Name name) {
        super(name, Sort.UPDATE, false, true);
    }

    @Override
    public String toString() {
        return toString("update");
    }

    @Override
    public String proofToString() {
        return "\\schemaVar \\update " + name() + ";\n";
    }
}