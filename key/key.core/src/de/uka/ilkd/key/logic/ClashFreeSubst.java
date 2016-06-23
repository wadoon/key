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

package de.uka.ilkd.key.logic;

import org.key_project.common.core.logic.CCClashFreeSubst;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.services.TermServices;

public class ClashFreeSubst extends CCClashFreeSubst<Visitor, Term> {

    public ClashFreeSubst(QuantifiableVariable v, Term s,
            TermServices services) {
        super(v, s, services, Term.class);
    }

    public static class VariableCollectVisitor extends
            CCClashFreeSubst.VariableCollectVisitor<Visitor, Term> implements
            Visitor {
        // Only here such that we have a class implementing the JavaDL Visitor
    }

}