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
package de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.visitor;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.java.AbstractProgramElement;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.prover.InstantiationAspectProverHelper;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.resultobjects.APERetrievalResult;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;

public class CollectAPEVisitor extends JavaASTVisitor {
    private final List<APERetrievalResult> result = new ArrayList<>();
    private final Proof proof;

    public CollectAPEVisitor(ProgramElement root, GoalLocalSpecificationRepository localSpecRepo,
            Services services) {
        super(root, localSpecRepo, services);
        this.proof = services.getProof();
    }

    @Override
    public void doDefaultAction(SourceElement node) {
        if (node instanceof AbstractProgramElement) {
            final AbstractProgramElement ape = (AbstractProgramElement) node;

            List<TextualJMLConstruct> jmlConstructs;
            try {
                jmlConstructs = Arrays
                        .stream(InstantiationAspectProverHelper
                                .parseMethodLevelComments(ape.getComments(), "DummyProblemFile"))
                        .collect(Collectors.toList());
            } catch (SLTranslationException e) {
                throw new RuntimeException("Could not parse APE comments", e);
            }

            result.add(new APERetrievalResult(ape, jmlConstructs, proof));
        }
    }

    public List<APERetrievalResult> getResult() {
        return result;
    }
}