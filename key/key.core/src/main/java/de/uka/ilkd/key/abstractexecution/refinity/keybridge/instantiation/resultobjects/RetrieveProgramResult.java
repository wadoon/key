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

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;

public class RetrieveProgramResult {
    private final Proof proof;
    private final JavaProgramElement program;

    public RetrieveProgramResult(JavaProgramElement program, Proof proof) {
        this.proof = proof;
        this.program = program;
    }

    public Proof getProof() {
        return proof;
    }

    public JavaProgramElement getProgram() {
        return program;
    }

    public Services getServices() {
        return proof.getServices();
    }

    public GoalLocalSpecificationRepository getLocalSpecRepo() {
        return proof.openGoals().head().getLocalSpecificationRepository();
    }
}