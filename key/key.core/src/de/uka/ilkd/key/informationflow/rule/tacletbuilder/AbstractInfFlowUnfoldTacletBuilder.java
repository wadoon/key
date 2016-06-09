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
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.op.SchemaVariable;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.proof.init.StateVars;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.Pair;


/**
 * Builds the rule which inserts information flow contract applications.
 * <p/>
 * @author christoph
 */
abstract class AbstractInfFlowUnfoldTacletBuilder extends AbstractInfFlowTacletBuilder {

    private static final String SCHEMA_PREFIX = "sv_";
    static final String UNFOLD = "unfold computed formula ";

    /** Counter to allow several side-proofs. */
    static int unfoldCounter = 0;

    private IFProofObligationVars ifVars;

    private JavaDLTerm replacewith;


    public AbstractInfFlowUnfoldTacletBuilder(Services services) {
        super(services);
    }


    public void setInfFlowVars(IFProofObligationVars ifVars) {
        this.ifVars = ifVars.labelHeapAtPreAsAnonHeapFunc();
    }


    public void setReplacewith(JavaDLTerm replacewith) {
        this.replacewith = replacewith;
    }


    public Taclet buildTaclet() {
        Name tacletName = getTacletName();
        unfoldCounter++;

        // create schema vars
        IFProofObligationVars schemaVars =
                generateApplicationDataSVs(ifVars, services);

        // create find term and replace information flow variables by
        // schema variables
        final JavaDLTerm find = createFindTerm(ifVars);
        JavaDLTerm schemaFind = replace(find, ifVars, schemaVars, services);

        // create replacewith term and replace information flow variables by
        // schema variables in the replacewith term, too
        JavaDLTerm schemaReplaceWith = replace(replacewith, ifVars, schemaVars, services);

        // collect quantifiable variables of the find term and replacewith term
        // and replace all quantifiable variables by schema variables
        Map<QuantifiableVariable, SchemaVariable> quantifiableVarsToSchemaVars =
                collectQuantifiableVariables(schemaFind, services);
        quantifiableVarsToSchemaVars.putAll(
                collectQuantifiableVariables(schemaReplaceWith, services));
	final OpReplacer or = new OpReplacer(quantifiableVarsToSchemaVars, tf());
	schemaFind = or.replace(schemaFind);
	schemaReplaceWith = or.replace(schemaReplaceWith);

        //create taclet
        final RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<RewriteTaclet>();
        tacletBuilder.setName(tacletName);
        tacletBuilder.setFind(schemaFind);
        tacletBuilder.setApplicationRestriction(RewriteTaclet.ANTECEDENT_POLARITY);
        final RewriteTacletGoalTemplate goal =
                new RewriteTacletGoalTemplate(schemaReplaceWith);
        tacletBuilder.addTacletGoalTemplate(goal);
        tacletBuilder.addRuleSet(new RuleSet(new Name("concrete")));
        tacletBuilder.setSurviveSmbExec(true);
        addVarconds(tacletBuilder, quantifiableVarsToSchemaVars.values());

        return tacletBuilder.getTaclet();
    }


    private IFProofObligationVars generateApplicationDataSVs(
            IFProofObligationVars ifVars,
            Services services) {
        return new IFProofObligationVars(
                generateApplicationDataSVs(SCHEMA_PREFIX, ifVars.c1, services),
                generateApplicationDataSVs(SCHEMA_PREFIX, ifVars.c2, services),
                ifVars.symbExecVars);
    }


    private ProofObligationVars generateApplicationDataSVs(String schemaPrefix,
                                                           ProofObligationVars poVars,
                                                           Services services) {
        Function n = services.getTheories().getHeapLDT().getNull();

        // generate a new schema variable for any pre variable
        JavaDLTerm selfAtPreSV =
                createTermSV(poVars.pre.self, schemaPrefix, services);
        ImmutableList<JavaDLTerm> localVarsAtPreSVs =
                createTermSV(poVars.pre.localVars, schemaPrefix, services);
        JavaDLTerm guardAtPreSV =
                createTermSV(poVars.pre.guard, schemaPrefix, services);
        JavaDLTerm resAtPreSV = null;
        JavaDLTerm excAtPreSV = null;
        JavaDLTerm heapAtPreSV =
                createTermSV(poVars.pre.heap, schemaPrefix, services);
        JavaDLTerm mbyAtPreSV =
                createTermSV(poVars.pre.mbyAtPre, schemaPrefix, services);

        // generate a new schema variable only for those post variables
        // which do not equal the corresponding pre variable; else use
        // the pre schema variable
        JavaDLTerm selfAtPostSV = (poVars.pre.self == poVars.post.self ?
                             selfAtPreSV :
                             createTermSV(poVars.post.self, schemaPrefix, services));

        ImmutableList<JavaDLTerm> localVarsAtPostSVs = ImmutableSLList.<JavaDLTerm>nil();
        Iterator<JavaDLTerm> appDataPreLocalVarsIt = poVars.pre.localVars.iterator();
        Iterator<JavaDLTerm> schemaLocalVarsAtPreIt = localVarsAtPreSVs.iterator();
        for (JavaDLTerm appDataPostLocalVar : poVars.post.localVars) {
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

        JavaDLTerm guardAtPostSV = (poVars.pre.guard == poVars.post.guard) ?
                             guardAtPreSV :
                             createTermSV(poVars.post.guard, schemaPrefix, services);
        JavaDLTerm resAtPostSV = (poVars.post.result == null ||
                            poVars.post.result.op().equals(n)) ?
                           null :
                           createTermSV(poVars.post.result, schemaPrefix, services);
        JavaDLTerm excAtPostSV = (poVars.post.exception == null ||
                            poVars.post.exception.op().equals(n)) ?
                           null :
                           createTermSV(poVars.post.exception, schemaPrefix, services);
        JavaDLTerm heapAtPostSV = (poVars.pre.heap == poVars.post.heap ?
                             heapAtPreSV :
                             createTermSV(poVars.post.heap, schemaPrefix, services));

        // build state variable container for pre and post state
        StateVars pre =
                new StateVars(selfAtPreSV, guardAtPreSV, localVarsAtPreSVs, resAtPreSV,
                              excAtPreSV, heapAtPreSV, mbyAtPreSV);
        pre = filterSchemaVars(poVars.pre, pre);
        StateVars post =
                new StateVars(selfAtPostSV, guardAtPostSV, localVarsAtPostSVs, resAtPostSV,
                              excAtPostSV, heapAtPostSV, null);
        post = filterSchemaVars(poVars.post, post);

        // return proof obligation schema variables
        return new ProofObligationVars(pre, post, poVars.exceptionParameter,
                                       poVars.formalParams, services);
    }


    private static JavaDLTerm replace(JavaDLTerm term,
                                IFProofObligationVars origVars,
                                IFProofObligationVars schemaVars,
                                Services services) {
        JavaDLTerm intermediateResult = replace(term, origVars.c1, schemaVars.c1, services);
        return replace(intermediateResult, origVars.c2, schemaVars.c2, services);
    }


    private static JavaDLTerm replace(JavaDLTerm term,
                                ProofObligationVars origVars,
                                ProofObligationVars schemaVars,
                                Services services) {
        JavaDLTerm intermediateResult = replace(term, origVars.pre, schemaVars.pre, services);
        return replace(intermediateResult, origVars.post, schemaVars.post, services);
    }


    private static JavaDLTerm replace(JavaDLTerm term,
                                StateVars origVars,
                                StateVars schemaVars,
                                Services services) {
        LinkedHashMap<JavaDLTerm, JavaDLTerm> map = new LinkedHashMap<JavaDLTerm, JavaDLTerm>();

        Pair<StateVars, StateVars> vars = filter(origVars, schemaVars);
        origVars = vars.first;
        schemaVars = vars.second;
        assert origVars.termList.size() == schemaVars.termList.size();
        Iterator<JavaDLTerm> origVarsIt = origVars.termList.iterator();
        Iterator<JavaDLTerm> schemaVarsIt = schemaVars.termList.iterator();
        while (origVarsIt.hasNext()) {
            JavaDLTerm origTerm = origVarsIt.next();
            JavaDLTerm svTerm = schemaVarsIt.next();
            if (origTerm != null && svTerm != null) {
                assert svTerm.sort().equals(origTerm.sort()) ||
                       svTerm.sort().extendsSorts().contains(origTerm.sort()) :
                        "mismatch of sorts: orignal term " + origTerm +
                        ", sort " + origTerm.sort() +
                        "; replacement term" + svTerm + ", sort " +
                        svTerm.sort();
                map.put(origTerm, svTerm);
            }
        }
        OpReplacer or = new OpReplacer(map, services.getTermFactory());
        JavaDLTerm result = or.replace(term);

        return result;
    }


    private static Pair<StateVars, StateVars> filter(StateVars origVars,
                                                     StateVars schemaVars) {
        schemaVars = filterSchemaVars(origVars, schemaVars);
        origVars = filterSchemaVars(schemaVars, origVars);
        return new Pair<StateVars, StateVars>(origVars, schemaVars);
    }


    private static StateVars filterSchemaVars(StateVars origVars,
                                              StateVars schemaVars) {
        if (origVars.termList.size() == schemaVars.termList.size()) {
            return schemaVars;
        }
        JavaDLTerm self = schemaVars.self;
        JavaDLTerm guard = schemaVars.guard;
        ImmutableList<JavaDLTerm> localVars = schemaVars.localVars;
        JavaDLTerm result = schemaVars.result;
        JavaDLTerm exception = schemaVars.exception;
        JavaDLTerm heap = schemaVars.heap;
        JavaDLTerm mbyAtPre = schemaVars.mbyAtPre;
        if (origVars.self == null) {
            self = null;
        }
        if (origVars.guard == null) {
            guard = null;
        }
        if (origVars.localVars == null) {
            localVars = null;
        } else if (origVars.localVars.isEmpty()) {
            localVars = ImmutableSLList.<JavaDLTerm>nil();
        }
        if (origVars.result == null) {
            result = null;
        }
        if (origVars.exception == null) {
            exception = null;
        }
        if (origVars.heap == null) {
            heap = null;
        }
        if (origVars.mbyAtPre == null) {
            mbyAtPre = null;
        }
        return new StateVars(self, guard, localVars, result, exception, heap, mbyAtPre);
    }


    abstract Name getTacletName();


    abstract JavaDLTerm createFindTerm(IFProofObligationVars ifVars);
}
