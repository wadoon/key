package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.TacletMatcher;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;

/**
 * Collection of static helper methods that are used in replay.
 *
 * @author Wolfram Pfeifer
 */
public final class ReplayTools {
    private ReplayTools() {
    }

    /**
     * Replaces a bound variable by another one in a term.
     * @param toReplace the variable to replace
     * @param with the new variable
     * @param in the Term to replace in
     * @param services Services needed to construct the new term
     * @return a new Term where every occurrence of the bound variable has been replaced with the
     *      new one
     */
    public static Term replace(QuantifiableVariable toReplace,
                               QuantifiableVariable with,
                               Term in,
                               Services services) {
        // using OpReplacer does not replace the QuantifiableVariables (due to missing equals
        // method?)
        // return OpReplacer.replace(tb.var(orig), tb.var(repl), t, tf);
        Operator newOp = in.op();
        if (newOp instanceof QuantifiableVariable
            && equalsOp((QuantifiableVariable) newOp, toReplace)) {
            newOp = with;
        }

        Term[] newTerms = new Term[in.subs().size()];
        for (int i = 0; i < newTerms.length; i++) {
            newTerms[i] = replace(toReplace, with, in.subs().get(i), services);
        }
        // note: bound vars must be bound in new term again!
        return services.getTermFactory().createTerm(newOp, newTerms, in.boundVars(), null);
    }

    /**
     * Gets the original text of the given context, i.e. the text as it was specified in the input.
     * In contrast to ctx.getText(), this includes the whitespace.
     * @param ctx the context to construct the original text
     * @return the original text of ctx with whitespace
     */
    public static String getOriginalText(ParserRuleContext ctx) {
        if (ctx.start == null || ctx.start.getStartIndex() < 0
            || ctx.stop == null || ctx.stop.getStopIndex() < 0) {
            // fallback
            return ctx.getText();
        }
        int start = ctx.start.getStartIndex();
        int end = ctx.stop.getStopIndex();
        return ctx.start.getInputStream().getText(Interval.of(start, end));
    }

    // TODO: replace by real equals method in QuantifiableVariable
    public static boolean equalsOp(QuantifiableVariable a, QuantifiableVariable b) {
        return a.name().equals(b.name()) && a.sort().equals(b.sort());
    }

    public static boolean eqDifferentPolarity(SequentFormula s1, SequentFormula s2) {
        Term t1 = s1.formula();
        Term t2 = s2.formula();
        if (t1.op() == Junctor.NOT) {
            return t1.sub(0).equals(t2);
        } else if (t2.op() == Junctor.NOT) {
            return t2.sub(0).equals(t1);
        }
        return false;
    }

    public static SequentFormula getLastModifiedAntec(Goal goal) {
        SequentChangeInfo sci = goal.node().getNodeInfo().getSequentChangeInfo();
        return sci.modifiedFormulas(true).head().getNewFormula();
    }

    public static SequentFormula getLastModifiedSuc(Goal goal) {
        SequentChangeInfo sci = goal.node().getNodeInfo().getSequentChangeInfo();
        return sci.modifiedFormulas(false).head().getNewFormula();
    }

    public static SequentFormula getLastAddedAntec(Goal goal) {
        SequentChangeInfo sci = goal.node().getNodeInfo().getSequentChangeInfo();
        return sci.addedFormulas(true).head();
    }

    public static SequentFormula getLastAddedAntec(Goal goal, int index) {
        SequentChangeInfo sci = goal.node().getNodeInfo().getSequentChangeInfo();
        return sci.addedFormulas(true).toList().get(index);
    }

    public static SequentFormula getLastAddedSuc(Goal goal) {
        SequentChangeInfo sci = goal.node().getNodeInfo().getSequentChangeInfo();
        return sci.addedFormulas(false).head();
    }

    public static SequentFormula getLastAddedSuc(Goal goal, int index) {
        SequentChangeInfo sci = goal.node().getNodeInfo().getSequentChangeInfo();
        return sci.addedFormulas(false).toList().get(index);
    }

    public static Goal applyNoSplitPosAntec(Goal goal, String tacletName, PosInTerm pit,
                                             SequentFormula sf) {
        PosInOccurrence pio = new PosInOccurrence(sf, pit, true);
        TacletApp app = createTacletApp(tacletName, pio, goal);
        return goal.apply(app).head();
    }

    public static Goal applyNoSplitTopLevelAntec(Goal goal, String tacletName, SequentFormula sf) {
        PosInOccurrence pio = new PosInOccurrence(sf, PosInTerm.getTopLevel(), true);
        TacletApp app = createTacletApp(tacletName, pio, goal);
        return goal.apply(app).head();
    }

    public static Goal applyNoSplitTopLevelSuc(Goal goal, String tacletName, SequentFormula sf) {
        PosInOccurrence pio = new PosInOccurrence(sf, PosInTerm.getTopLevel(), false);
        TacletApp app = createTacletApp(tacletName, pio, goal);
        return goal.apply(app).head();
    }


    public static TacletApp createTacletApp(String tacletName, PosInOccurrence pos, Goal goal) {
        TacletApp app = goal.indexOfTaclets().lookup(tacletName);
        System.out.println("Creating TacletApp " + tacletName);
        return autoInst(app, pos, goal);
    }

    // automatically instantiates taclet from PosInOccurrence, only works for taclets where all
    // instantiations are determined by the position
    public static TacletApp autoInst(TacletApp app, PosInOccurrence pos, Goal goal) {
        Services services = goal.proof().getServices();
        Term posTerm = pos.subTerm();
        app = app.setPosInOccurrence(pos, services);

        // automatically find instantiations for matching find term
        TacletMatcher matcher = app.taclet().getMatcher();
        // use app.matchConditions(): must not overwrite fixed instantiations
        // (e.g. insert_hidden taclet)
        MatchConditions current = app.matchConditions();
        MatchConditions mc = matcher.matchFind(posTerm, current, services);
        app = app.setMatchConditions(mc, services);

        // automatically find formulas for matching assume
        app = app.findIfFormulaInstantiations(goal.sequent(), services).head();

        // automatically create and register skolem symbols if required
        if (!app.complete()) {
            TacletApp skApp = app.tryToInstantiate(services);
            if (skApp != null) {
                // contains new skolem constants
                return skApp;
            }
        }

        return app;
    }

    public static NoPosTacletApp createCutApp(Goal goal, Term cutFormula) {
        NoPosTacletApp app = goal.indexOfTaclets().lookup("cut");
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();
        // since all branches in addInstantiation return NoPosTacletApp,
        // the cast should always be safe
        Services services = goal.proof().getServices();
        return (NoPosTacletApp) app.addInstantiation(sv, cutFormula, true, services);
    }
}