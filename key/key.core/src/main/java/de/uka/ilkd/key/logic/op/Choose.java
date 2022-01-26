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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

/**
 * This singleton class implements a Hilbert's choice operator, often denoted by epsilon.
 * "\choose x; (phi)", where x is a logic variable, phi is a formula (x is bound in phi).
 */
public final class Choose extends AbstractOperator {
    public static final Choose CHOOSE = new Choose();

    private Choose() {
	    super(new Name("choose"), 1, new Boolean[]{true}, true);
    }

    @Override
    public Sort sort(Term term) {
        return term.boundVars().get(0).sort();
    }

    @Override
    public Sort sort(ImmutableArray<Term> terms) {
        // TODO: might crash when called
        return null;
    }

    @Override
    protected void additionalValidTopLevel(Term term) {
        final Sort s0 = term.sub(0).sort();
        if (s0 != Sort.FORMULA) {
            throw new TermCreationException(this, term);
        }
    }
}