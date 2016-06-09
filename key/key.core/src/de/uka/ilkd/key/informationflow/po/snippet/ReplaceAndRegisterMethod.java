/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.informationflow.po.snippet;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Map;

import org.key_project.common.core.logic.Namespace;
import org.key_project.common.core.logic.Visitor;
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.informationflow.proof.init.StateVars;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.LinkedHashMap;


/**
 * Generate term "self != null".
 * <p/>
 * @author christoph
 */
abstract class ReplaceAndRegisterMethod {

    final JavaDLTerm replace(JavaDLTerm term,
                       ProofObligationVars origVars,
                       ProofObligationVars poVars,
                       TermBuilder tb) {
        JavaDLTerm intermediateResult = replace(term, origVars.pre, poVars.pre, tb);
        return replace(intermediateResult, origVars.post, poVars.post, tb);
    }


    final JavaDLTerm replace(JavaDLTerm term,
                       StateVars origVars,
                       StateVars poVars,
                       TermBuilder tb) {
        LinkedHashMap<JavaDLTerm, JavaDLTerm> map = new LinkedHashMap<JavaDLTerm, JavaDLTerm>();

        Iterator<JavaDLTerm> origVarsIt;
        Iterator<JavaDLTerm> poVarsIt;
        assert origVars.paddedTermList.size() ==
               poVars.paddedTermList.size();
        origVarsIt = origVars.paddedTermList.iterator();
        poVarsIt = poVars.paddedTermList.iterator();
        while (origVarsIt.hasNext()) {
            JavaDLTerm origTerm = origVarsIt.next();
            JavaDLTerm poTerm = poVarsIt.next();
            if (origTerm != null && poTerm != null) {
                assert poTerm.sort().equals(origTerm.sort()) ||
                       poTerm.sort().extendsSorts().contains(origTerm.sort()) :
                        "mismatch of sorts: orignal term " + origTerm +
                        ", sort " + origTerm.sort() +
                        "; replacement term" + poTerm + ", sort " +
                        poTerm.sort();
                map.put(origTerm, poTerm);
            }
        }
        OpReplacer or = new OpReplacer(map, tb.tf());
        JavaDLTerm result = or.replace(term);

        return result;
    }


    final JavaDLTerm[] replace(JavaDLTerm[] terms,
                         StateVars origVars,
                         StateVars poVars,
                         TermBuilder tb) {
        final JavaDLTerm[] result = new JavaDLTerm[terms.length];
        for (int i = 0; i < terms.length; i++) {
            result[i] = replace(terms[i], origVars, poVars, tb);

        }
        return result;
    }


    final InfFlowSpec replace(InfFlowSpec terms,
                              StateVars origVars,
                              StateVars poVars,
                              TermBuilder tb) {
        ImmutableList<JavaDLTerm> resultPreExps = ImmutableSLList.<JavaDLTerm>nil();
        for (JavaDLTerm t : terms.preExpressions) {
            resultPreExps = resultPreExps.append(replace(t, origVars, poVars, tb));
        }
        ImmutableList<JavaDLTerm> resultPostExps = ImmutableSLList.<JavaDLTerm>nil();
        for (JavaDLTerm t : terms.postExpressions) {
            resultPostExps = resultPostExps.append(replace(t, origVars, poVars, tb));
        }
        ImmutableList<JavaDLTerm> resultNewObjecs = ImmutableSLList.<JavaDLTerm>nil();
        for (JavaDLTerm t : terms.newObjects) {
            resultNewObjecs = resultNewObjecs.append(replace(t, origVars, poVars, tb));
        }
        return new InfFlowSpec(resultPreExps, resultPostExps, resultNewObjecs);
    }


    final InfFlowSpec[] replace(ImmutableList<InfFlowSpec> termss,
                                StateVars origVars,
                                StateVars poVars,
                                TermBuilder tb) {
        final InfFlowSpec[] result = new InfFlowSpec[termss.size()];
        Iterator<InfFlowSpec> it = termss.iterator();
        for (int i = 0; it.hasNext(); i++) {
            result[i] = replace(it.next(), origVars, poVars, tb);
        }
        return result;
    }


    final JavaDLTerm replace(JavaDLTerm term,
                       JavaDLTerm[] origVars,
                       JavaDLTerm[] poVars,
                       TermBuilder tb) {
        LinkedHashMap<JavaDLTerm, JavaDLTerm> map = new LinkedHashMap<JavaDLTerm, JavaDLTerm>();

        assert origVars.length == poVars.length;
        for (int i = 0; i < origVars.length; i++) {
            JavaDLTerm origTerm = origVars[i];
            JavaDLTerm poTerm = poVars[i];
            if (origTerm != null && poTerm != null) {
                assert origTerm.sort().equals(poTerm.sort());
                map.put(origTerm, poTerm);
            }
        }

        OpReplacer or = new OpReplacer(map, tb.tf());
        JavaDLTerm result = or.replace(term);

        return result;
    }


    final void register(ProgramVariable pv,
                        Services services) {
        Namespace progVarNames = services.getNamespaces().programVariables();
        if (pv != null && progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }


    final void register(ImmutableList<ProgramVariable> pvs,
                        Services services) {
        for (ProgramVariable pv : pvs) {
            register(pv, services);
        }
    }


    final void register(Function f,
                        Services services) {
        Namespace functionNames = services.getNamespaces().functions();
        if (f != null && functionNames.lookup(f.name()) == null) {
            assert f.sort() != Sort.UPDATE;
            functionNames.addSafely(f);
        }
    }

    final static JavaDLTerm replaceQuantifiableVariables(JavaDLTerm term,
                                             HashSet<QuantifiableVariable> qvs,
                                             Services services) {
        Map<QuantifiableVariable, QuantifiableVariable> replaceMap =
                new LinkedHashMap<QuantifiableVariable, QuantifiableVariable>();
        for (QuantifiableVariable qv: qvs) {
            replaceMap.put(qv, new LogicVariable(qv.name(), qv.sort()));
        }
        final OpReplacer op = new OpReplacer(replaceMap, services.getTermFactory());
        return op.replace(term);
    }

    final static HashSet<QuantifiableVariable> collectQuantifiableVariables(JavaDLTerm term) {
        QuantifiableVariableVisitor qvVisitor = new QuantifiableVariableVisitor();
        term.execPreOrder(qvVisitor);
        return qvVisitor.getResult();
    }

    final private static class QuantifiableVariableVisitor implements Visitor {
        private HashSet<QuantifiableVariable> vars = new LinkedHashSet<QuantifiableVariable>();

        @Override
        public boolean visitSubtree(JavaDLTerm visited) {
            return true;
        }

        @Override
        public void visit(JavaDLTerm visited) {
            final ImmutableArray<QuantifiableVariable> boundVars = visited.boundVars();
            for (QuantifiableVariable var : boundVars) vars.add(var);
        }

        @Override
        public void subtreeEntered(JavaDLTerm subtreeRoot) { /* nothing to do */ }

        @Override
        public void subtreeLeft(JavaDLTerm subtreeRoot) { /* nothing to do */ }

        public HashSet<QuantifiableVariable> getResult() { return vars; }
    }
}