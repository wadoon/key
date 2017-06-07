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

package de.tud.cs.se.ds.specstr.util;

import java.util.stream.Collectors;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;

/**
 * TODO
 *
 * @author Dominic Steinhöfel
 */
public class CNFConverter {
    private TermBuilder tb;
    private TermFactory tf;

    /**
     * 
     * @param tb
     */
    public CNFConverter(TermBuilder tb) {
        this.tb = tb;
        this.tf = tb.tf();
    }

    /**
     * TODO
     * 
     * @param t
     * @return
     */
    public Term convertToCNF(Term t) {
        // TODO: We can also convert formulas inside universal quantifiers into
        // CNF and split them then; do this later.

        return eliminateBiImplications(t);
    }

    public Term eliminateBiImplications(Term t) {
        if (t.op() == Junctor.IMP) {
            return tb.or(tb.not(eliminateBiImplications(t.sub(0))),
                    eliminateBiImplications(t.sub(1)));
        } else if (t.op() == Equality.EQV) {
            return tb.and(
                    tb.or( //
                            tb.not(eliminateBiImplications(t.sub(0))),
                            eliminateBiImplications(t.sub(1))),
                    tb.or( //
                            tb.not(eliminateBiImplications(t.sub(1))),
                            eliminateBiImplications(t.sub(0))));
        } else {
            return tf.createTerm( //
                    t.op(), //
                    GeneralUtilities.toStream(t.subs())
                            .map(sub -> eliminateBiImplications(sub))
                            .collect(Collectors.toList())
                            .toArray(new Term[] {}));
        }
    }
}
