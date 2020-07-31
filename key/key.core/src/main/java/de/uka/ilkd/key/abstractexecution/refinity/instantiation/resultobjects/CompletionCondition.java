// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.instantiation.resultobjects;

import java.util.Optional;

import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;

/**
 * A pre- and postcondition pair for one completion mode of an APE.
 * 
 * @author Dominic Steinhoefel
 */
public class CompletionCondition {
    private final Behavior behavior;
    private final Optional<String> javaDLPrecondition;
    private final Optional<String> javaDLPostcondition;

    public CompletionCondition(final Behavior behavior, final String javaDLPrecondition,
            final String javaDLPostcondition) {
        this.behavior = behavior;
        this.javaDLPrecondition = Optional.ofNullable(javaDLPrecondition);
        this.javaDLPostcondition = Optional.ofNullable(javaDLPostcondition);
    }

    public Behavior getBehavior() {
        return behavior;
    }

    public Optional<String> getJavaDLPrecondition() {
        return javaDLPrecondition;
    }

    public Optional<String> getJavaDLPostcondition() {
        return javaDLPostcondition;
    }

}
