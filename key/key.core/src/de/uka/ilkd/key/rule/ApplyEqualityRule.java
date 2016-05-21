package de.uka.ilkd.key.rule;

import java.util.HashMap;
import java.util.Map;

import org.key_project.util.LRUCache;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
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

    private static final Name NAME = new Name("ApplyEquality");

    public static final ApplyEqualityRule INSTANCE = new ApplyEqualityRule();

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) throws RuleAbortException {

        Pair<PosInOccurrence, Term> appl = applyTo(goal, ruleApp.posInOccurrence());
        if(appl == null) {
            throw new RuleAbortException("Cannot apply that rule any longer");
        }

        ImmutableList<Goal> result = goal.split(1);
        Goal newGoal = result.head();
        newGoal.changeFormula(new SequentFormula(appl.second), appl.first);

        return result;
    }

    public boolean canApply(Goal goal, RuleApp ruleApp) {
        Pair<PosInOccurrence, Term> appl = applyTo(goal, ruleApp.posInOccurrence());
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

        return true;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    private Pair<PosInOccurrence, Term> applyTo(Goal goal, PosInOccurrence pio) {

        Sequent seq = goal.sequent();

//        if(appCache.containsKey(seq)) {
//            return appCache.get(seq);
//        }

        Pair<PosInOccurrence, Term> result = null;

        Services services = goal.proof().getServices();
        Map<Term, Term> table = buildEqTable(seq, pio, services);
        if(!table.isEmpty()) {
            result = scanEquality(seq, pio, table, services);
        }

//        appCache.put(seq, result);
        return result;
    }

    private Pair<PosInOccurrence, Term> scanEquality(Sequent seq, PosInOccurrence pio, Map<Term, Term> table, Services services) {

        SequentFormula sequentFormula  = pio.sequentFormula();
        Term term = sequentFormula.formula();
        Term newTerm = replaceRecursive(term, table, services);
        if(newTerm != term) {
            return new Pair<PosInOccurrence, Term>(pio, newTerm);
        }

        return null;
    }

    private Term replaceRecursive(Term t, Map<Term, Term> table, Services services) {
        Term lookup = table.get(t);
        if(lookup != null) {
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
            Term newChild = replaceRecursive(oldChild, table, services);
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

    private Map<Term, Term> buildEqTable(Sequent seq, PosInOccurrence pio, Services services) {
        Map<Term, Term> result = new HashMap<Term, Term>();

        Term trueConst = services.getTermBuilder().tt();
        Term falseConst = services.getTermBuilder().ff();
        SequentFormula exclude = pio.sequentFormula();

        for (SequentFormula sequentFormula : seq.antecedent()) {
            if(sequentFormula == exclude) {
                continue;
            }
            Term formula = sequentFormula.formula();
            Operator op = formula.op();
            if(op == Equality.EQUALS) {
                result.put(formula.sub(0), formula.sub(1));
            }
            result.put(formula, trueConst);
        }

        for (SequentFormula sequentFormula : seq.succedent()) {
            if(sequentFormula == exclude) {
                continue;
            }
            Term formula = sequentFormula.formula();
            result.put(formula, falseConst);
        }

        return result;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new DefaultBuiltInRuleApp(this, pos);
    }

}
