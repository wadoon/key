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
 * "\some iv; (phi)", where iv is a logic variable, phi is a formula.
 * The variable iv is bound in phi.
 */
public final class Some extends AbstractOperator {
    public static final Some SOME = new Some();

    private Some() {
	    super(new Name("some"), 1, new Boolean[]{true}, true);
    }

    @Override
    public Sort sort(ImmutableArray<Term> terms) {
        // The sort of (\some ...) is always ANY, make sure to add a cast when creating
        // terms with \some. This allows us to have only a single operator \some instead of one
        // for each sort.
        // TODO: At the moment, via manual cuts it is probably possible to prove false!
        return Sort.ANY;
    }

    @Override
    protected void additionalValidTopLevel(Term term) {

        final Sort s0 = term.sub(0).sort();
        //final Sort s1 = term.sub(1).sort();

        if (s0 != Sort.FORMULA) {
            throw new TermCreationException(this, term);
        }
    }
}