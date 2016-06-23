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

package org.key_project.bytecode.core.logic.op;

import org.key_project.bytecode.core.logic.InstructionBlock;
import org.key_project.bytecode.core.logic.Term;
import org.key_project.bytecode.core.logic.visitors.Visitor;
import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.op.CCWarySubstOp;
import org.key_project.common.core.services.TermServices;

public final class WarySubstOp extends CCWarySubstOp<InstructionBlock, Visitor, Term> {

    /**
     * the wary substitution operator {var<-term}'. {x<-d}'A(x) means replace
     * all free occurrences of variable x in A with d, however without replacing
     * x with a non-rigid A below modalities
     */
    public static final WarySubstOp SUBST = new WarySubstOp(new Name("subst"));

    private WarySubstOp(Name name) {
        super(name);
    }

    @Override
    public Term apply(Term term, TermServices services) {
        return super.apply(term, services, Term.class);
    }
}