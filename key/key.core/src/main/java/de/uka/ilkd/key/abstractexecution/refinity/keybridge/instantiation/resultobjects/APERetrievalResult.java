// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.resultobjects;

import java.util.List;

import de.uka.ilkd.key.abstractexecution.java.AbstractProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;

public class APERetrievalResult {
    public final int line;
    private final AbstractProgramElement ape;
    private final List<TextualJMLConstruct> jmlConstructs;
    private final Proof proof;

    public APERetrievalResult(final AbstractProgramElement ape,
            final List<TextualJMLConstruct> jmlConstructs, final Proof proof) {
        this.ape = ape;
        this.jmlConstructs = jmlConstructs;
        // There's a shift of 3 lines in the dummy Java file.
        this.line = ape.getStartPosition().getLine() - 3;
        this.proof = proof;
    }

    public AbstractProgramElement getApe() {
        return ape;
    }

    public List<TextualJMLConstruct> getJMLConstructs() {
        return jmlConstructs;
    }

    public int getLine() {
        return line;
    }

    public Services getServices() {
        return proof.getServices();
    }

    public GoalLocalSpecificationRepository getLocalSpecRepo() {
        return proof.openGoals().head().getLocalSpecificationRepository();
    }
}