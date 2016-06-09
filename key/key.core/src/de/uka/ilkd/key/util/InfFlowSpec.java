/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.util;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.JavaDLTerm;


/**
 *
 * @author christoph
 */
public class InfFlowSpec {
    public static final InfFlowSpec EMPTY_INF_FLOW_SPEC = new InfFlowSpec();

    public final ImmutableList<JavaDLTerm> preExpressions;

    public final ImmutableList<JavaDLTerm> postExpressions;

    public final ImmutableList<JavaDLTerm> newObjects;


    public InfFlowSpec(final ImmutableList<JavaDLTerm> preExpressions,
                       final ImmutableList<JavaDLTerm> postExpressions,
                       final ImmutableList<JavaDLTerm> newObjects) {
        this.preExpressions = preExpressions;
        this.postExpressions = postExpressions;
        this.newObjects = newObjects;
    }

    private InfFlowSpec() {
        this.preExpressions = ImmutableSLList.<JavaDLTerm>nil();
        this.postExpressions = ImmutableSLList.<JavaDLTerm>nil();
        this.newObjects = ImmutableSLList.<JavaDLTerm>nil();
    }
}
