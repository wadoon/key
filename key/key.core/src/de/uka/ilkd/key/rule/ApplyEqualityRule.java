package de.uka.ilkd.key.rule;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.key_project.util.LRUCache;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.util.Pair;

public class ApplyEqualityRule implements BuiltInRule {

    private static class ReplacementMap {

        private static final PosInTerm PIO_TOP_LEVEL = PosInTerm.getTopLevel();
        private static final PosInTerm PIO_RHS = PIO_TOP_LEVEL.down(1);
        private Map<Term, List<PosInOccurrence>> map;
        private final Term trueConst;
        private final Term falseConst;

        public ReplacementMap(Services services) {
            trueConst = services.getTermBuilder().tt();
            falseConst = services.getTermBuilder().ff();
        }

        public Term lookup(Term t, PosInOccurrence avoid) {
            List<PosInOccurrence> pios = map.get(t);
            if(pios == null) {
                return null;
            }

            for (PosInOccurrence pio : pios) {
                // do not apply onto the formula itself
                if(pio.topLevel().equals(avoid)) {
                    continue;
                }

                if(pio.isTopLevel()) {
                    return pio.isInAntec() ? trueConst : falseConst;
                } else {
                    return pio.subTerm();
                }
            }
            return null;
        }

        public void scan(Sequent seq) {

            map = new HashMap<Term, List<PosInOccurrence>>();

            for (SequentFormula sequentFormula : seq.antecedent()) {
                Term formula = sequentFormula.formula();
                Operator op = formula.op();
                if(op == Equality.EQUALS) {
                    add(formula.sub(0), new PosInOccurrence(sequentFormula, PIO_RHS, true));
                }
                add(formula, new PosInOccurrence(sequentFormula, PIO_TOP_LEVEL, true));
            }

            for (SequentFormula sequentFormula : seq.succedent()) {
                Term formula = sequentFormula.formula();
                add(formula, new PosInOccurrence(sequentFormula, PIO_TOP_LEVEL, false));
            }

        }

        private void add(Term term, PosInOccurrence pio) {
             List<PosInOccurrence> list = map.get(term);
             if(list == null) {
                 list = new LinkedList<>();
                 map.put(term, list);
             }
             list.add(pio);
        }

    }


    private static final Name NAME = new Name("ApplyEquality");

    public static final ApplyEqualityRule INSTANCE = new ApplyEqualityRule();

    private final Map<Sequent, ReplacementMap> eqTableCache = new LRUCache<>(10);

    private final Map<Pair<Goal, PosInOccurrence>, Term> appCache = new LRUCache<>(300);

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) throws RuleAbortException {

        Term appl = applyTo(goal, ruleApp.posInOccurrence());
        if(appl == null) {
            throw new RuleAbortException("Cannot apply that rule any longer");
        }

        ImmutableList<Goal> result = goal.split(1);
        Goal newGoal = result.head();
        newGoal.changeFormula(new SequentFormula(appl), ruleApp.posInOccurrence());

        DefaultBuiltInRuleApp birRuleApp = (DefaultBuiltInRuleApp)ruleApp;

        return result;
    }

    public boolean canApply(Goal goal, RuleApp ruleApp) {
        Object appl = applyTo(goal, ruleApp.posInOccurrence());
        return appl != null;
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
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        if(pio == null) {
            return false;
        }

        return pio.isTopLevel();
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    private Term applyTo(Goal goal, PosInOccurrence pio) {

        Sequent seq = goal.sequent();

        if(appCache.containsKey(new Pair<>(goal, pio))) {
            return appCache.get(seq);
        }

        Term result = null;

        Services services = goal.proof().getServices();
        ReplacementMap table = buildEqTable(seq, services);
        result = scanEquality(seq, pio, table, services);

//        appCache.put(new Pair<>(goal, pio), result);
        return result;
    }

    private Term scanEquality(Sequent seq, PosInOccurrence pio,
                ReplacementMap table, Services services) {

        SequentFormula sequentFormula  = pio.sequentFormula();
        Term term = sequentFormula.formula();

        Term newTerm = replaceRecursive(term, table, services, pio);


        if(newTerm != term) {
            return newTerm;
        }

        return null;
    }

    private Term replaceRecursive(Term t, ReplacementMap table, Services services,
            PosInOccurrence avoid) {
        Term lookup = table.lookup(t, avoid);
        if(lookup != null) {

            // since we iterate over this term, == can be used here!
            if(t.sort() != lookup.sort()) {
                lookup = services.getTermBuilder().cast(t.sort(), lookup);
            }
            return lookup;
        }

        Operator op = t.op();
        if(op == UpdateApplication.UPDATE_APPLICATION || op instanceof Modality) {
            return t;
        }

        ImmutableArray<Term> children = t.subs();
        Term[] newChildren = new Term[children.size()];
        boolean changed = false;
        for (int i = 0; i < children.size(); i++) {
            Term oldChild = children.get(i);
            Term newChild = replaceRecursive(oldChild, table, services, avoid);
            newChildren[i] = newChild;
            if(newChild != oldChild) {
                changed = true;
            }
        }

        if(!changed) {
            return t;
        } else {
            return services.getTermFactory().createTerm(op, newChildren, t.boundVars(), t.javaBlock());
        }
    }

    private ReplacementMap buildEqTable(Sequent seq, Services services) {

        ReplacementMap result = eqTableCache.get(seq);
        if (result != null) {
            return result;

        }

        result = new ReplacementMap(services);
        result.scan(seq);

//        eqTableCache.put(seq, result);
        return result;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new DefaultBuiltInRuleApp(this, pos);
    }

    @Override
    public String toString() {
        return NAME.toString();
    }
}
