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
package de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.prover;

import java.util.Map;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.abstractexecution.java.AbstractProgramElement;
import de.uka.ilkd.key.abstractexecution.java.statement.AbstractStatement;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.resultobjects.ProofResult;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.resultobjects.RetrieveProgramResult;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.CreatingASTVisitor;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;
import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * Proves that specified <tt>ae_constraint</tt>s are satisfied.
 * 
 * NOT YET IMPLEMENTED.
 * 
 * @author Dominic Steinhoefel
 */
public class AEConstraintsProver implements InstantiationAspectProver {
    private final InstantiationAspectProverHelper helper;

    public AEConstraintsProver() {
        helper = new InstantiationAspectProverHelper();
    }

    public AEConstraintsProver(final Profile profile) {
        helper = new InstantiationAspectProverHelper(profile);
    }

    @Override
    public ProofResult prove(final AEInstantiationModel model) {
        final RetrieveProgramResult retrProgRes = helper.retrieveProgram(model, model.getProgram());
        final JavaProgramElement abstractProgram = retrProgRes.getProgram();
        final GoalLocalSpecificationRepository localSpecRepo = retrProgRes.getLocalSpecRepo();
        final Services services = retrProgRes.getServices();
        
        // instantiate APEs
        final InstantiateAPEsVisitor instAPEsVisitor = new InstantiateAPEsVisitor(abstractProgram, true,
                localSpecRepo, services);

        return ProofResult.EMPTY;
    }

    @Override
    public String initMessage() {
        return "[NOT YET IMPLEMENTED] Proving " + proofObjective() + "...";
    }

    @Override
    public String proofObjective() {
        return "validity of instantiated assumptions";
    }
    
    private Map<AbstractProgramElement, JavaProgramElement> apeInsts(final AEInstantiationModel model) {
        final Map<AbstractProgramElement, JavaProgramElement> result = new LinkedHashMap<>();
        
        
        
        return result;
    }

    private static class InstantiateAPEsVisitor extends CreatingASTVisitor {
        public InstantiateAPEsVisitor(ProgramElement root, boolean preservesPos,
                GoalLocalSpecificationRepository localSpecRepo, Services services) {
            super(root, preservesPos, localSpecRepo, services);
        }

        @Override
        public void performActionOnAbstractStatement(AbstractStatement x) {
            DefaultAction def = new DefaultAction(x) {
                @Override
                protected ProgramElement createNewElement(ExtList changeList) {
                    AbstractStatement newAbstrStmt = new AbstractStatement(changeList);
                    performActionOnAbstractProgramElementContract(x, newAbstrStmt);
                    return newAbstrStmt;
                }
            };
            def.doAction(x);
        }
    }

}
