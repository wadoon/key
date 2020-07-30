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
package de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.proginst;

import java.util.List;
import java.util.Optional;
import java.util.regex.Matcher;

import org.antlr.runtime.RecognitionException;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.prover.InstantiationAspectProverHelper;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation.resultobjects.RetrieveProgramResult;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.APEInstantiation;
import de.uka.ilkd.key.abstractexecution.refinity.util.KeyBridgeUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * Instantiates an abstract program.
 * 
 * @author Dominic Steinhoefel
 */
public class AbstractProgramInstantiator {
    private final AEInstantiationModel model;
    private final InstantiationAspectProverHelper helper;

    public AbstractProgramInstantiator(final AEInstantiationModel model,
            final InstantiationAspectProverHelper helper) {
        this.model = model;
        this.helper = helper;
    }

    public String instantiate() throws RecognitionException {
        final RetrieveProgramResult retrRes = helper.retrieveProgram(model, model.getProgram());
        final Services services = retrRes.getServices();
        model.fillNamespacesFromNewInstsUnsafe(services);

        final LightweightAbstractProgramParser parser = //
                new LightweightAbstractProgramParser(model.getProgram());
        parser.parse();

        final List<ProgramSegment> segments = parser.mergedProgramSegments();

        final StringBuilder progSb = new StringBuilder();
        for (final ProgramSegment segment : segments) {
            if (segment instanceof AEConstraintSegment) {
                final AEConstraintSegment constrSeg = (AEConstraintSegment) segment;

                final String prefixedTerm = KeyBridgeUtils
                        .dlPrefixRigidModelElements(model.getAbstractLocationSets(),
                                model.getPredicateDeclarations(), model.getFunctionDeclarations(),
                                helper.substituteLocsetValueInstsInString(
                                        constrSeg.getFormulaContent(), model))
                        .replaceAll("([^\\\\])singletonPV\\b", "$1\\\\dl_singletonPV")
                        .replaceAll("\\bPV\\b", Matcher.quoteReplacement("\\dl_PV"));

                /* non-final */ Term instTerm = KeyBridgeUtils.jmlStringToJavaDLTerm(prefixedTerm,
                        KeyBridgeUtils.dummyKJT(),
                        (ProgramVariable) services.getNamespaces().programVariables()
                                .lookup("result"),
                        services.getNamespaces().programVariables().allElements().stream()
                                .map(ProgramVariable.class::cast)
                                .collect(ImmutableSLList.toImmutableList()),
                        services);

                instTerm = helper.instantiateTerm(instTerm, model, services);
                
                // TODO: Translate the term to a JML representation, easiest by prefixing all functions with "\dl_".
                //       Also, pretty-print to get rid of the Z terms.

                progSb.append("//@ assert ").append(KeyBridgeUtils.termToString(instTerm, services))
                        .append(";\n{ ; }\n");
            } else if (segment instanceof AbstractStatementProgramSegment) {
                final AbstractStatementProgramSegment asSeg = (AbstractStatementProgramSegment) segment;
                final Optional<APEInstantiation> maybeInst = model.getApeInstantiations().stream()
                        .filter(inst -> inst.getApeLineNumber() == asSeg.getLine()).findFirst();
                if (maybeInst.isPresent()) {
                    progSb.append("{ ").append(maybeInst.get().getInstantiation()).append(" }\n");
                } else {
                    progSb.append(segment.getContent()).append("\n");
                }
            } else {
                progSb.append(segment.getContent()).append("\n");
            }
        }

        return progSb.toString();
    }

}
