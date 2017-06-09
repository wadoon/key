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

package de.tud.cs.se.ds.specstr.logic.label;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;

/**
 * TODO
 *
 * @author Dominic Steinhöfel
 */
public class StrengthAnalysisParameterlessTL implements TermLabel {

    public static final Name FACT_LABEL_NAME = new Name("fact");

    /**
     * Label attached to the formula representing a fact to prove.
     */
    public static final TermLabel FACT_LABEL = //
            new StrengthAnalysisParameterlessTL(FACT_LABEL_NAME);

    ///////////////////

    public static final Name FACT_PREMISE_LABEL_NAME = new Name("factPremise");

    /**
     * Label attached to the formula representing the premise for a fact, e.g. a
     * loop invariant or a post condition.
     */
    public static final TermLabel FACT_PREMISE_LABEL = //
            new StrengthAnalysisParameterlessTL(FACT_PREMISE_LABEL_NAME);

    ///////////////////

    private ParameterlessTermLabel delegate;

    public StrengthAnalysisParameterlessTL(Name name) {
        this.delegate = new ParameterlessTermLabel(name);
    }

    @Override
    public Name name() {
        return delegate.name();
    }

    @Override
    public Object getChild(int i) {
        return delegate.getChild(i);
    }

    @Override
    public int getChildCount() {
        return delegate.getChildCount();
    }

    @Override
    public String toString() {
        return delegate.toString();
    }

}
