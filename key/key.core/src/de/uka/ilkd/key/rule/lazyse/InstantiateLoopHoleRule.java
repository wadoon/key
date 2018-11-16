// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.lazyse;

import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Instantiates "wholes" left by symbolic execution of while loops (by the
 * "lazyLoop" taclet, currently).
 *
 * <strong>IMPORTANT:</strong> Usage of this rule is only sound if a
 * corresponding side proof showing that the instantiation is correct, i.e.,
 * that the loop respects the contract substituted here for the holes. This is
 * why of now (2018-11-16), this rule should never be applied automatically.
 *
 * @author Dominic Steinhöfel
 */
public class InstantiateLoopHoleRule implements BuiltInRule {
    /**
     * The name of the lazy SE taclet corresponding to loop treatment.
     */
    public static final String LAZY_LOOP_TACLET_NAME = "lazyLoop";
    public static final BuiltInRule INSTANCE = new InstantiateLoopHoleRule();

    private final static Name NAME = new Name("Instantiate Loop Holes");

    private InstantiateLoopHoleRule() {
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) throws RuleAbortException {
        final ImmutableList<Goal> newGoals = goal.split(1);
        final LoopHoleInstantiation loopHoleInst = //
                ((InstantiateLoopHoleRuleApp) ruleApp)
                        .getLoopHoleInstantiation();
        final LoopHole loopHole = loopHoleInst.getLoopHole();
        final Goal newGoal = newGoals.head();

        Sequent sequent = newGoal.sequent();
        SequentChangeInfo sci = null;

        for (int i = 0; i < sequent.antecedent().size(); i++) {
            final SequentFormula sf = sequent.antecedent().get(i);
            final Term formula = sf.formula();
            final Operator op = formula.op();
            final PosInOccurrence pio = new PosInOccurrence(sf,
                PosInTerm.getTopLevel(), true);

            if (op instanceof Function && formula.subs().isEmpty() && op.name()
                    .toString().equals(loopHole.getPathCondPlaceholder())) {
                sci = sequent.changeFormula(
                    new SequentFormula(loopHoleInst.getPathCondInst()), pio);
                sequent = sci.sequent();
                break;
            }
        }

        for (int i = 0; i < sequent.succedent().size(); i++) {
            final SequentFormula sf = sequent.succedent().get(i);
            final Term formula = sf.formula();
            final Operator op = formula.op();
            final PosInOccurrence pio = new PosInOccurrence(sf,
                PosInTerm.getTopLevel(), false);

            if (op instanceof UpdateApplication) {
                final Term substTerm = substitute(formula,
                    t -> t.sort() == Sort.UPDATE && t.op() instanceof Function
                            && t.op().name().toString()
                                    .equals(loopHole.getSymbStorePlaceholder()),
                    loopHoleInst.getSymbStoreInst(), services.getTermFactory());
                if (!substTerm.equals(formula)) {
                    sci.combine(sequent
                            .changeFormula(new SequentFormula(substTerm), pio));
                }
            }
        }

        newGoal.setSequent(sci);

        return newGoals;
    }

    private Term substitute(Term in, MatchCond matchCond, Term by,
            TermFactory tf) {
        if (matchCond.matches(in)) {
            return by;
        }

        final Term[] subs = new Term[in.subs().size()];
        int i = 0;
        for (Term sub : in.subs()) {
            subs[i] = substitute(sub, matchCond, by, tf);
            i++;
        }

        return tf.createTerm(in.op(), subs, in.boundVars(), in.javaBlock(),
            in.getLabels());
    }

    @FunctionalInterface
    private static interface MatchCond {
        boolean matches(Term t);
    }

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

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        return true;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos,
            TermServices services) {
        return new InstantiateLoopHoleRuleApp(null);
    }

    /**
     * Traverses the proof tree and returns all loop holes, which correspond to
     * "lazyLoop" taclet applications.
     *
     * @param proof
     *            The {@link Proof} to traverse.
     * @return An array of all "lazyLoop" rule applications.
     */
    public static LoopHole[] retrieveLoopHoles(Proof proof) {
        final Iterable<Node> nodes = () -> proof.root().subtreeIterator();
        final List<Node> lazyLoopRuleNodes = //
                StreamSupport.stream(nodes.spliterator(), false)
                        .filter(node -> node.getAppliedRuleApp() != null) //
                        .filter(node -> node.getAppliedRuleApp().rule().name()
                                .toString().equals(LAZY_LOOP_TACLET_NAME))
                        .collect(Collectors.toList());

        final LoopHole[] result = new LoopHole[lazyLoopRuleNodes.size()];
        for (int i = 0; i < result.length; i++) {
            final Node node = lazyLoopRuleNodes.get(i);
            final PosTacletApp posTacletApp = //
                    (PosTacletApp) node.getAppliedRuleApp();
            final While loop = (While) JavaTools.getActiveStatement(TermBuilder
                    .goBelowUpdates(posTacletApp.posInOccurrence().subTerm())
                    .javaBlock());
            final SVInstantiations instantiations = //
                    posTacletApp.instantiations();

            final String pcPlaceholderName = instantiations
                    .lookupValue(new Name("C_sk")).toString();
            final String symbStPlaceholderName = instantiations
                    .lookupValue(new Name("U_sk")).toString();

            result[i] = new LoopHole(i + 1, pcPlaceholderName,
                symbStPlaceholderName, node, loop);
        }

        return result;
    }

}
