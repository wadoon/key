/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.informationflow.po.snippet;


import java.util.Iterator;

import org.key_project.common.core.logic.op.Function;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.util.InfFlowSpec;

/**
 * Generate term "self != null".
 *
 * @author christoph
 */
class InfFlowInputOutputRelationSnippet extends ReplaceAndRegisterMethod
    implements InfFlowFactoryMethod {
    @Override
    public JavaDLTerm produce(BasicSnippetData d,
                        ProofObligationVars poVars1,
                        ProofObligationVars poVars2)
            throws UnsupportedOperationException {
        // get information flow specification terms
        if (d.get(BasicSnippetData.Key.INF_FLOW_SPECS) == null) {
            throw new UnsupportedOperationException("Tried to produce " +
                    "information flow relations for a contract without " +
                    "information flow specification.");
        }
        assert ImmutableList.class.equals(BasicSnippetData.Key.INF_FLOW_SPECS.getType());
        @SuppressWarnings("unchecked")
        ImmutableList<InfFlowSpec>
            origInfFlowSpecs =
                (ImmutableList<InfFlowSpec>) d.get(BasicSnippetData.Key.INF_FLOW_SPECS);

        // the information-flow-specification-sequents evaluated in the pre-state
        InfFlowSpec[] infFlowSpecsAtPre1 = replace(origInfFlowSpecs, d.origVars, poVars1.pre, d.tb);
        InfFlowSpec[] infFlowSpecsAtPre2 = replace(origInfFlowSpecs, d.origVars, poVars2.pre, d.tb);

        // the information-flow-specification-sequents evaluated in the post-state
        InfFlowSpec[] infFlowSpecsAtPost1 = replace(origInfFlowSpecs, d.origVars, poVars1.post, d.tb);
        InfFlowSpec[] infFlowSpecsAtPost2 = replace(origInfFlowSpecs, d.origVars, poVars2.post, d.tb);

        // create input-output-relations
        final JavaDLTerm[] relations = new JavaDLTerm[infFlowSpecsAtPre1.length];
        for (int i = 0; i < infFlowSpecsAtPre1.length; i++) {
            relations[i] = buildInputOutputRelation(d, poVars1, poVars2,
                                                    infFlowSpecsAtPre1[i],
                                                    infFlowSpecsAtPre2[i],
                                                    infFlowSpecsAtPost1[i],
                                                    infFlowSpecsAtPost2[i]);
        }

        return d.tb.and(relations);
    }


    private JavaDLTerm buildInputOutputRelation(BasicSnippetData d,
                                          ProofObligationVars vs1,
                                          ProofObligationVars vs2,
                                          InfFlowSpec infFlowSpecAtPre1,
                                          InfFlowSpec infFlowSpecAtPre2,
                                          InfFlowSpec infFlowSpecAtPost1,
                                          InfFlowSpec infFlowSpecAtPost2) {
        JavaDLTerm inputRelation =
                buildInputRelation(d, vs1, vs2, infFlowSpecAtPre1,
                                   infFlowSpecAtPre2);
        JavaDLTerm outputRelation =
                buildOutputRelation(d, vs1, vs2, infFlowSpecAtPost1,
                                    infFlowSpecAtPost2);

        return d.tb.imp(inputRelation,
                        d.tb.label(outputRelation,
                                   ParameterlessTermLabel.POST_CONDITION_LABEL));
    }


    private JavaDLTerm buildInputRelation(BasicSnippetData d,
                                    ProofObligationVars vs1,
                                    ProofObligationVars vs2,
                                    InfFlowSpec infFlowSpec1,
                                    InfFlowSpec infFlowSpec2) {
        JavaDLTerm[] eqAtLocs = new JavaDLTerm[infFlowSpec1.preExpressions.size()];

        Iterator<JavaDLTerm> preExp1It = infFlowSpec1.preExpressions.iterator();
        Iterator<JavaDLTerm> preExp2It = infFlowSpec2.preExpressions.iterator();
        for (int i = 0; i < infFlowSpec1.preExpressions.size(); i++) {
            JavaDLTerm preExp1Term = preExp1It.next();
            JavaDLTerm preExp2Term = preExp2It.next();
            SearchVisitor search = new SearchVisitor(vs1.pre.result, vs1.post.result);
            preExp1Term.execPreOrder(search);
            if (!search.termFound) {
                eqAtLocs[i] =
                        d.tb.equals(preExp1Term, preExp2Term);
            } else {
                // terms which contain \result are not included in
                // the precondition
                eqAtLocs[i] = d.tb.tt();
            }
        }

        return d.tb.and(eqAtLocs);
    }

    private JavaDLTerm buildOutputRelation(BasicSnippetData d,
                                     ProofObligationVars vs1,
                                     ProofObligationVars vs2,
                                     InfFlowSpec infFlowSpec1,
                                     InfFlowSpec infFlowSpec2) {
        // build equalities for post expressions
        ImmutableList<JavaDLTerm> eqAtLocs = ImmutableSLList.<JavaDLTerm>nil();

        Iterator<JavaDLTerm> postExp1It = infFlowSpec1.postExpressions.iterator();
        Iterator<JavaDLTerm> postExp2It = infFlowSpec2.postExpressions.iterator();
        for (int i = 0; i < infFlowSpec1.postExpressions.size(); i++) {
            JavaDLTerm postExp1Term = postExp1It.next();
            JavaDLTerm postExp2Term = postExp2It.next();
            eqAtLocs = eqAtLocs.append(d.tb.equals(postExp1Term, postExp2Term));
        }
        final JavaDLTerm eqAtLocsTerm = d.tb.and(eqAtLocs);

        if (infFlowSpec1.newObjects.isEmpty()) {
            // object insensitive case
            return eqAtLocsTerm;
        } else {
            // object sensitive case
            return buildObjectSensitivePostRelation(infFlowSpec1, infFlowSpec2,
                                                    d, vs1, vs2, eqAtLocsTerm);
        }
    }


    protected JavaDLTerm buildObjectSensitivePostRelation(InfFlowSpec infFlowSpec1,
                                                    InfFlowSpec infFlowSpec2,
                                                    BasicSnippetData d,
                                                    ProofObligationVars vs1,
                                                    ProofObligationVars vs2,
                                                    JavaDLTerm eqAtLocsTerm) {
        // build equalities for newObjects terms
        ImmutableList<JavaDLTerm> newObjEqs = ImmutableSLList.<JavaDLTerm>nil();
        Iterator<JavaDLTerm> newObjects1It = infFlowSpec1.newObjects.iterator();
        Iterator<JavaDLTerm> newObjects2It = infFlowSpec2.newObjects.iterator();
        for (int i = 0; i < infFlowSpec1.newObjects.size(); i++) {
            JavaDLTerm newObject1Term = newObjects1It.next();
            JavaDLTerm newObject2Term = newObjects2It.next();
            newObjEqs = newObjEqs.append(d.tb.equals(newObject1Term, newObject2Term));
        }
        final JavaDLTerm newObjEqsTerm = d.tb.and(newObjEqs);

        // build isomorphism term for newObjects
        final JavaDLTerm newObjsSeq1 = d.tb.seq(infFlowSpec1.newObjects);
        final JavaDLTerm newObjsSeq2 = d.tb.seq(infFlowSpec2.newObjects);
        final Function newObjectsIso =
                (Function)d.services.getNamespaces().functions().lookup("newObjectsIsomorphic");
        final JavaDLTerm isoTerm = d.tb.func(newObjectsIso, newObjsSeq1, vs1.pre.heap,
                                       newObjsSeq2, vs2.pre.heap);

        // build object oriented post-relation (object sensitive case)
        final JavaDLTerm ooPostRelation =
                d.tb.and(isoTerm, d.tb.imp(newObjEqsTerm, eqAtLocsTerm));
        if (vs1.pre.guard != null && vs1.post.guard != null
                && vs2.pre.guard != null && vs2.post.guard != null) {
            // Case of loop invariants.
            // In this case newObjecs is only considered in case the
            // loop body is entered. Otherwise no code is executed an
            // hence also no objects can be created.
            final JavaDLTerm preGuardFalse1 = d.tb.equals(vs1.pre.guard, d.tb.FALSE());
            final JavaDLTerm preGuardFalse2 = d.tb.equals(vs2.pre.guard, d.tb.FALSE());
            return d.tb.ife(d.tb.and(preGuardFalse1, preGuardFalse2),
                            eqAtLocsTerm, ooPostRelation);
        } else {
            // Normal case.
            return ooPostRelation;
        }
    }


    private static class SearchVisitor extends DefaultVisitor {

        private boolean termFound = false;
        private JavaDLTerm[] searchTerms;

        public SearchVisitor(JavaDLTerm... searchTerms) {
            this.searchTerms = searchTerms;
        }

        @Override
        public void visit(JavaDLTerm visited) {
            for (JavaDLTerm searchTerm : searchTerms) {
                termFound = termFound || visited.equals(searchTerm);
            }
        }
    }
}
