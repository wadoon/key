// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.SuperReference;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.IntIterator;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.UseOperationContractRule.Instantiation;
import de.uka.ilkd.key.speclang.jml.JMLInfoExtractor;


public final class MethodCallToLogicRule implements BuiltInRule {

    public static final MethodCallToLogicRule INSTANCE = new MethodCallToLogicRule();

    private static final Name NAME = new Name("Method Call To Logic");

    private static Term lastFocusTerm;
    private static Instantiation lastInstantiation;


    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    private MethodCallToLogicRule() { }

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    @Override
    public Name name() {
        return NAME;
    }


    @Override
    public String displayName() {
        return NAME.toString();
    }


    @Override
    public String toString() {
        return displayName();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new DefaultBuiltInRuleApp(this, pos);
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {

        // focus must be top level succedent
        if(pio == null || !pio.isTopLevel() || pio.isInAntec()) {
            return false;
        }

        // instantiation must succeed
        final Instantiation inst =
                instantiate(pio.subTerm(),
                        goal.proof().getServices());

        if(inst == null) {
            return false;
        }

        // abort if inside of transformer
        if (Transformer.inTransformer(pio)) {
            return false;
        }

        if(!JMLInfoExtractor.isStrictlyPure(inst.pm)
                && !inst.pm.isModel()) {
            // Perhaps JMLInfoExtractor.isStrictlyPureByDefault(XX) needs be checked too
            return false;
        }

        return true;
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) {

        // get instantiation
        final Instantiation inst =
                instantiate(ruleApp.posInOccurrence().subTerm(), services);
        final JavaBlock jb = inst.progPost.javaBlock();
        final TermBuilder tb = services.getTermBuilder();

        // create heap variable.
        final Term baseHeapTerm = tb.getBaseHeap();

        // create result variable
        final LocationVariable resultVar = tb.resultVar(inst.pm, true);
        Term resultTerm = tb.var(resultVar);

        // create the function application
        // XXX What to do with no_state and two_state model methods?
        int i = inst.pm.isStatic() ? 1 : 2;
        
        Term[] args = new Term[inst.actualParams.size() + i];
        args[0] = baseHeapTerm;
        
        if (!inst.pm.isStatic()) {
        	args[1] = inst.actualSelf;
        }
        for (Term arg : inst.actualParams) {
            args[i] = arg;
            i++;
        }
        Term application = tb.tf().createTerm(inst.pm, args);

        // create update
        Term update = tb.elementary(resultTerm, application);

        // split goal into three branches
        final ImmutableList<Goal> result;
        final Goal preGoal, postGoal, nullGoal;
        final ReferencePrefix rp = inst.mr.getReferencePrefix();
        if(rp != null
                && !(rp instanceof ThisReference)
                && !(rp instanceof SuperReference)
                && !(rp instanceof TypeReference)
                && !(inst.pm.isStatic())) {
            result = goal.split(3);
            postGoal = result.get(2);
            preGoal = result.get(1);
            nullGoal = result.head();
            nullGoal.setBranchLabel("Null reference ("
                    + inst.actualSelf
                    + " = null)");
        } else {
            result = goal.split(2);
            postGoal = result.get(1);
            preGoal = result.head();
            nullGoal = null;
        }

        preGoal.setBranchLabel("XXX Pre");
        postGoal.setBranchLabel("Normal behaviour");

        // --- precondition goal
        /// XXX This is dummy at the moment
        preGoal.changeFormula(new SequentFormula(tb.tt()), ruleApp.posInOccurrence());

        // --- create "Post" branch
        CopyAssignment ca = new CopyAssignment(inst.actualResult, resultVar);
        StatementBlock resultAssign = new StatementBlock(ca);
        StatementBlock postSB = UseOperationContractRule.replaceStatement(jb, resultAssign);
        JavaBlock postJavaBlock = JavaBlock.createJavaBlock(postSB);
        Term contTerm = tb.apply(update, tb.prog(inst.mod, postJavaBlock,inst.progPost.sub(0)));

        SequentFormula contFormula = replace(ruleApp, inst, tb, contTerm);
        postGoal.changeFormula(contFormula, ruleApp.posInOccurrence());

        // -- create "Null Reference" branch
        if(nullGoal != null) {
            final Term actualSelfNotNull = tb.not(tb.equals(inst.actualSelf, tb.NULL()));
            contFormula = replace(ruleApp, inst, tb, actualSelfNotNull);
            nullGoal.changeFormula(contFormula, ruleApp.posInOccurrence());
        }

        // -- create justification
        //    perhaps this is needed ?!

        return result;
    }

    private SequentFormula replace(RuleApp ruleApp, final Instantiation inst, final TermBuilder tb,
            Term contTerm) {
        SequentFormula sf = ruleApp.posInOccurrence().sequentFormula();
        Term replacement = replace(sf.formula(), ruleApp.posInOccurrence().posInTerm().iterator(), contTerm, tb.tf());
        SequentFormula contFormula = new SequentFormula(tb.apply(inst.u, replacement));
        return contFormula;
    }

    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------

    private Term replace(Term term, IntIterator posIterator, Term newTerm, TermFactory tf) {
        if(posIterator.hasNext()) {
            int idx = posIterator.next();
            Term[] subs = term.subs().toArray(new Term[term.arity()]);
            subs[idx] = replace(subs[idx], posIterator, newTerm, tf);

            return tf.createTerm(term.op(),
                    subs,
                    term.boundVars(),
                    term.javaBlock(),
                    term.getLabels());
        } else {
            return newTerm;
        }
    }

    private static Instantiation instantiate(Term focusTerm, Services services) {
        //result cached?
        if(focusTerm == lastFocusTerm) {
            return lastInstantiation;
        }

        //compute
        final Instantiation result =
                UseOperationContractRule.computeInstantiation(focusTerm, services);

        //cache and return
        lastFocusTerm = focusTerm;
        lastInstantiation = result;
        return result;
    }




}