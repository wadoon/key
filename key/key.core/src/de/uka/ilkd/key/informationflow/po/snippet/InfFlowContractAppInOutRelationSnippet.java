/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.informationflow.po.snippet;


import java.util.Iterator;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.util.InfFlowSpec;

/**
 *
 * @author christoph
 */
class InfFlowContractAppInOutRelationSnippet extends InfFlowInputOutputRelationSnippet {

    // In case of the application of an information flow contract we can
    // assume the identity on the newly created objects, as opposed to the
    // proof obligation where we have to show that there is an isomorphism.
    @Override
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

        // build object oriented post-relation for contract applications
        return d.tb.and(eqAtLocsTerm, newObjEqsTerm);
    }

}
