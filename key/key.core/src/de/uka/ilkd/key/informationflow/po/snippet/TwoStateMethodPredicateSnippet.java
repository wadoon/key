/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.informationflow.po.snippet;

import java.util.Iterator;
import java.util.List;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.Namespace;
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.LoopInvariant;


/**
 * Generate term "self != null".
 * <p/>
 * @author christoph
 */
abstract class TwoStateMethodPredicateSnippet implements FactoryMethod {

    @Override
    public JavaDLTerm produce(BasicSnippetData d,
                        ProofObligationVars poVars)
            throws UnsupportedOperationException {

        IObserverFunction targetMethod =
                (IObserverFunction) d.get(BasicSnippetData.Key.TARGET_METHOD);
        final IProgramMethod pm = (IProgramMethod) targetMethod;
        StatementBlock targetBlock =
                (StatementBlock) d.get(BasicSnippetData.Key.TARGET_BLOCK);
        LoopInvariant loopInv =
                (LoopInvariant) d.get(BasicSnippetData.Key.LOOP_INVARIANT);
        String nameString = generatePredicateName(pm, targetBlock, loopInv);
        final ImmutableList<JavaDLTerm> termList =
                extractTermListForPredicate(pm, poVars, d.hasMby);
        final Sort[] argSorts =
                generateContApplArgumentSorts(termList, pm);
        final Function contApplPred =
                generateContApplPredicate(nameString, argSorts, d.tb, d.services);
        return instantiateContApplPredicate(contApplPred, termList, d.tb);
    }

    protected Sort[] generateContApplArgumentSorts(
            ImmutableList<JavaDLTerm> termList, IProgramMethod pm) {

        Sort[] argSorts = new Sort[termList.size()];
        ImmutableArray<Sort> pmSorts = pm.argSorts();

        int i = 0;
        for (final JavaDLTerm arg : termList) {
            argSorts[i] = arg.sort();
            i++;
        }

        return argSorts;
    }


    private Function generateContApplPredicate(String nameString,
                                               Sort[] argSorts,
                                               TermBuilder tb,
                                               Services services) {
        final Name name = new Name(nameString);
        final Namespace functionNS = services.getNamespaces().functions();
        Function pred = (Function) functionNS.lookup(name);

        if (pred == null) {
            pred = new Function(name, Sort.FORMULA, argSorts);
            services.getNamespaces().functions().addSafely(pred);
        }
        return pred;
    }


    private JavaDLTerm instantiateContApplPredicate(Function pred,
                                              ImmutableList<JavaDLTerm> termList,
                                              TermBuilder tb) {
        final Sort[] predArgSorts = new Sort[pred.argSorts().size()];
        pred.argSorts().toArray(predArgSorts);
        JavaDLTerm[] predArgs = new JavaDLTerm[predArgSorts.length];

        int i = 0;
        for (final JavaDLTerm arg : termList) {
            predArgs[i] = arg;
            i++;
        }

        return tb.func(pred, predArgs);
    }


    abstract String generatePredicateName(IProgramMethod pm,
                                          StatementBlock block,
                                          LoopInvariant loopInv);


    /**
     * Parameters and the result of a method only have to appear once in the
     * predicate. This method chooses the right variables out of the poVars.
     * @param poVars    The proof obligation variables.
     * @return
     */
    private ImmutableList<JavaDLTerm> extractTermListForPredicate(
            IProgramMethod pm,
            ProofObligationVars poVars,
            boolean hasMby) {
        ImmutableList<JavaDLTerm> relevantPreVars = ImmutableSLList.<JavaDLTerm>nil();
        ImmutableList<JavaDLTerm> relevantPostVars = ImmutableSLList.<JavaDLTerm>nil();

        if (!pm.isStatic()) {
            // self is relevant in the pre and post state for constructors
            // (if the method is static, then there is no self)
            relevantPreVars = relevantPreVars.append(poVars.pre.self);
            relevantPostVars = relevantPostVars.append(poVars.post.self);
        }

        // local variables which are not changed during execution or whose
        // changes are not observable (like for parameters) are relevant only
        // in the pre state
        Iterator<JavaDLTerm> localPostVarsIt = poVars.post.localVars.iterator();
        for (JavaDLTerm localPreVar : poVars.pre.localVars) {
            JavaDLTerm localPostVar = localPostVarsIt.next();
            relevantPreVars = relevantPreVars.append(localPreVar);
            if (localPostVar != localPreVar) {
                relevantPostVars = relevantPostVars.append(localPostVar);
            }
        }

        // guard term (for loop invariants) is relevant in the pre and
        // post state
        if (poVars.pre.guard != null) {
            // in case of an information flow loop invariant
            assert poVars.post.guard != null;
            relevantPreVars = relevantPreVars.append(poVars.pre.guard);
            relevantPostVars = relevantPostVars.append(poVars.post.guard);
        }

        // the result and possible exceptions are relevant only in the post
        // state
        if (poVars.post.result != null) {
            // method is not void
            relevantPostVars = relevantPostVars.append(poVars.post.result);
        }
        if (poVars.post.exception != null) {
            // TODO: only null for loop invariants?
            relevantPostVars = relevantPostVars.append(poVars.post.exception);
        }

        if (hasMby) {
            // if the contract has a mesured by clause, then mbyAtPre is also
            // relevant
            relevantPreVars = relevantPreVars.append(poVars.pre.mbyAtPre);
        }

        // the heap is relevant in the pre and post state
        relevantPreVars = relevantPreVars.append(poVars.pre.heap);
        relevantPostVars = relevantPostVars.append(poVars.post.heap);

        return relevantPreVars.append(relevantPostVars);
    }
}