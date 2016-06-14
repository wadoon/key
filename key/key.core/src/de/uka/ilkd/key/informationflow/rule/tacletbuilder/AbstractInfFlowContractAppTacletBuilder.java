// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.informationflow.rule.tacletbuilder;

import java.util.Iterator;
import java.util.Map;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.op.SchemaVariable;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.informationflow.proof.init.StateVars;
import de.uka.ilkd.key.informationflow.rule.InfFlowContractAppTaclet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApplPart;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.TacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.TacletPrefixBuilder;


/**
 * Builds the rule which inserts information flow contract applications.
 *
 * @author christoph
 */
abstract class AbstractInfFlowContractAppTacletBuilder extends AbstractInfFlowTacletBuilder {

    private JavaDLTerm[] contextUpdates;
    private ProofObligationVars poVars;
    static final String USE_IF = InfFlowContractAppTaclet.USE_IF;
    private static final String IF_CONTRACT_APPLICATION = "information_flow_contract_appl";

    public AbstractInfFlowContractAppTacletBuilder(final Services services) {
        super(services);
    }

    public void setContextUpdate(JavaDLTerm... contextUpdates) {
        this.contextUpdates = contextUpdates;
    }


    public void setProofObligationVars(ProofObligationVars poVars) {
        this.poVars = poVars;
    }


    public JavaDLTerm buildContractApplPredTerm() {
        ProofObligationVars appData = poVars;
        JavaDLTerm contractApplPredTerm = getContractApplPred(appData);
        for (JavaDLTerm update : contextUpdates) {
            contractApplPredTerm = apply(update, contractApplPredTerm);
        }
        return contractApplPredTerm;
    }


    public Taclet buildTaclet() {
        ProofObligationVars appData = poVars;
        return genInfFlowContractApplTaclet(appData, services);
    }


    abstract Name generateName();

    private static Name checkName(Name name) {
        int i = 0;
        final String s = name.toString();
        while (InfFlowContractAppTaclet.registered(name)) {
            name = new Name(s + "_" + i++);
        }
        InfFlowContractAppTaclet.register(name);
        return name;
    }

    abstract JavaDLTerm generateSchemaAssumes(ProofObligationVars schemaDataAssumes,
                                        Services services);


    abstract JavaDLTerm generateSchemaFind(ProofObligationVars schemaDataFind,
                                     Services services);


    abstract JavaDLTerm getContractApplPred(ProofObligationVars appData);


    ProofObligationVars generateApplicationDataSVs(String schemaPrefix,
                                                   ProofObligationVars appData,
                                                   Services services) {
        // generate a new schema variable for any pre variable
        JavaDLTerm selfAtPreSV =
                createTermSV(appData.pre.self, schemaPrefix, services);
        ImmutableList<JavaDLTerm> localVarsAtPreSVs =
                createTermSV(appData.pre.localVars, schemaPrefix, services);
        JavaDLTerm guardAtPreSV =
                createTermSV(appData.pre.guard, schemaPrefix, services);
        JavaDLTerm resAtPreSV =
                createTermSV(appData.pre.result, schemaPrefix, services);
        JavaDLTerm excAtPreSV =
                createTermSV(appData.pre.exception, schemaPrefix, services);
        JavaDLTerm heapAtPreSV =
                createTermSV(appData.pre.heap, schemaPrefix, services);
        JavaDLTerm mbyAtPreSV =
                createTermSV(appData.pre.mbyAtPre, schemaPrefix, services);

        // generate a new schema variable only for those post variables
        // which do not equal the corresponding pre variable; else use
        // the pre schema variable
        JavaDLTerm selfAtPostSV = (appData.pre.self == appData.post.self ?
                selfAtPreSV :
                createTermSV(appData.post.self, schemaPrefix, services));

        ImmutableList<JavaDLTerm> localVarsAtPostSVs = ImmutableSLList.<JavaDLTerm>nil();
        Iterator<JavaDLTerm> appDataPreLocalVarsIt = appData.pre.localVars.iterator();
        Iterator<JavaDLTerm> schemaLocalVarsAtPreIt = localVarsAtPreSVs.iterator();
        for (JavaDLTerm appDataPostLocalVar : appData.post.localVars) {
            JavaDLTerm appDataPreLocalVar = appDataPreLocalVarsIt.next();
            JavaDLTerm localPreVar = schemaLocalVarsAtPreIt.next();
            if (appDataPostLocalVar == appDataPreLocalVar) {
                localVarsAtPostSVs = localVarsAtPostSVs.append(localPreVar);
            } else {
                localVarsAtPostSVs =
                        localVarsAtPostSVs.append(createTermSV(appDataPostLocalVar,
                                                               schemaPrefix,
                                                               services));
            }
        }

        JavaDLTerm guardAtPostSV = (appData.pre.guard == appData.post.guard ?
                guardAtPreSV :
                createTermSV(appData.post.guard, schemaPrefix, services));
        JavaDLTerm resAtPostSV = (appData.pre.result == appData.post.result ?
                resAtPreSV :
                createTermSV(appData.post.result, schemaPrefix, services));
        JavaDLTerm excAtPostSV = (appData.pre.exception == appData.post.exception ?
                excAtPreSV :
                createTermSV(appData.post.exception, schemaPrefix, services));
        JavaDLTerm heapAtPostSV = (appData.pre.heap == appData.post.heap ?
                heapAtPreSV :
                createTermSV(appData.post.heap, schemaPrefix, services));

        // build state vararibale container for pre and post state
        StateVars pre =
                new StateVars(selfAtPreSV, guardAtPreSV,
                              localVarsAtPreSVs, resAtPreSV,
                              excAtPreSV, heapAtPreSV,
                              mbyAtPreSV);
        StateVars post =
                new StateVars(selfAtPostSV, guardAtPostSV,
                              localVarsAtPostSVs, resAtPostSV,
                              excAtPostSV, heapAtPostSV,
                              null);

        // return proof obligation schema variables
        return new ProofObligationVars(pre, post, poVars.exceptionParameter,
                                       poVars.formalParams, services);
    }


    private Taclet genInfFlowContractApplTaclet(ProofObligationVars appData,
                                                Services services) {
        Name tacletName = checkName(generateName());
            // generate schemaFind and schemaAssumes terms
            ProofObligationVars schemaDataFind =
                    generateApplicationDataSVs("find_", appData, services);
            JavaDLTerm schemaFind = generateSchemaFind(schemaDataFind, services);
            ProofObligationVars schemaDataAssumes =
                    generateApplicationDataSVs("assumes_", appData, services);
            JavaDLTerm schemaAssumes = generateSchemaAssumes(schemaDataAssumes, services);

            // generate post term
            JavaDLTerm replaceWithTerm =
                    buildContractApplications(schemaDataFind,
                                              schemaDataAssumes, services);

            // collect quantifiable variables of the post term and replace them
            // by schema variables
            Map<QuantifiableVariable, SchemaVariable> quantifiableVarsToSchemaVars =
                    collectQuantifiableVariables(schemaFind, services);
            quantifiableVarsToSchemaVars.putAll(
                    collectQuantifiableVariables(schemaAssumes, services));
            quantifiableVarsToSchemaVars.putAll(
                    collectQuantifiableVariables(replaceWithTerm, services));
            final OpReplacer or = new OpReplacer(quantifiableVarsToSchemaVars,
                                                 services.getTermFactory());
            schemaFind = or.replace(schemaFind);
            schemaAssumes = or.replace(schemaAssumes);
            replaceWithTerm = or.replace(replaceWithTerm);

            //create sequents
            Sequent assumesSeq = Sequent.createAnteSequent(
                    new Semisequent(new SequentFormula(schemaAssumes)));
            Sequent replaceWithSeq = Sequent.createAnteSequent(
                    new Semisequent(new SequentFormula(replaceWithTerm)));

            //create taclet
            InfFlowContractAppRewriteTacletBuilder tacletBuilder =
                    new InfFlowContractAppRewriteTacletBuilder();
            tacletBuilder.setName(tacletName);
            tacletBuilder.setFind(schemaFind);
            tacletBuilder.setApplicationRestriction(RewriteTaclet.ANTECEDENT_POLARITY);
            tacletBuilder.setIfSequent(assumesSeq);
            RewriteTacletGoalTemplate goalTemplate =
                    new RewriteTacletGoalTemplate(replaceWithSeq,
                                                  ImmutableSLList.<Taclet>nil(),
                                                  schemaFind);
            tacletBuilder.addTacletGoalTemplate(goalTemplate);
            tacletBuilder.addRuleSet(new RuleSet(new Name(IF_CONTRACT_APPLICATION)));
            tacletBuilder.setSurviveSmbExec(true);
            addVarconds(tacletBuilder, quantifiableVarsToSchemaVars.values());
            return tacletBuilder.getTaclet();
    }


    abstract JavaDLTerm buildContractApplications(ProofObligationVars contAppData,
                                            ProofObligationVars contAppData2,
                                            Services services);


    /**
     * A normal RewriteTacletBuilder except that an InfFlowContractAppTaclet is
     * returned instead of a normal RewriteTaclet.  InfFlowContractAppTaclet's
     * are normal RewriteTaclet's except that the formula which is added by the
     * taclets are also added to the list of formulas contained in the
     * INF_FLOW_CONTRACT_APPL_PROPERTY. The INF_FLOW_CONTRACT_APPL_PROPERTY is
     * used by the macros UseInformationFlowContractMacro and
     * PrepareInfFlowContractPreBranchesMacro to decide how to prepare the
     * formulas resulting from information flow contract applications.
     */
    private class InfFlowContractAppRewriteTacletBuilder extends RewriteTacletBuilder<InfFlowContractAppTaclet> {

        InfFlowContractAppRewriteTacletBuilder() {
        }


        @Override
        public InfFlowContractAppTaclet getRewriteTaclet() {
            if (find == null) {
                throw new TacletBuilder.TacletBuilderException(this, "No find part specified");

            }
            checkBoundInIfAndFind();
            TacletPrefixBuilder prefixBuilder = new TacletPrefixBuilder(this);
            prefixBuilder.build();
            return new InfFlowContractAppTaclet(name,
                                     new TacletApplPart(ifseq,
                                                        varsNew,
                                                        varsNotFreeIn,
                                                        varsNewDependingOn,
                                                        variableConditions),
                                     goals, ruleSets,
                                     attrs,
                                     find,
                                     prefixBuilder.getPrefixMap(),
                                     applicationRestriction,
                                     choices,
                                     surviveSmbExec, tacletAnnotations);

        }
    }
}
