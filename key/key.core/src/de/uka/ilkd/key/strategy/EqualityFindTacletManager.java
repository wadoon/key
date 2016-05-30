package de.uka.ilkd.key.strategy;

import java.util.Map;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.util.LinkedHashMap;

public class EqualityFindTacletManager implements GeneralFindTacletAppManager {

    private static final Name EQ_NAME = new Name("applyEq");

    private final Map<Term, ImmutableList<RuleAppContainer>> table =
            new LinkedHashMap<>();

    private Goal goal;

    @Override
    public boolean isResponsible(RuleAppContainer c) {
        boolean equals = c.getRuleApp().rule().name().equals(EQ_NAME);
        if(equals) {
            return c instanceof FindTacletAppContainer;
        }
        return false;
    }

    @Override
    public void add(RuleAppContainer c) {
        FindTacletAppContainer findCntainer = (FindTacletAppContainer)c;
        PosInOccurrence pio = findCntainer.getPosInOccurrence(goal);
        Term term = pio.subTerm();
        ImmutableList<RuleAppContainer> list = table.get(term);
        if(list == null) {
            list = ImmutableSLList.<RuleAppContainer>nil();
        }
        table.put(term, list.prepend(c));
    }

    @Override
    public Iterable<RuleAppContainer> getMatchingRuleApps(Goal goal) {

        ImmutableList<RuleAppContainer> result = ImmutableSLList.<RuleAppContainer>nil();

        Semisequent antecedent = goal.node().sequent().antecedent();
        for (SequentFormula seqFormula : antecedent) {
            Term formula = seqFormula.formula();
            Operator op = formula.op();
            if(op == Equality.EQUALS) {
                Term lhs = formula.sub(0);
                ImmutableList<RuleAppContainer> matchingApps = table.get(lhs);
                if(matchingApps != null) {
                    result = result.prepend(matchingApps);
                    table.remove(lhs);
                }
            }
        }

        return result;
    }

    @Override
    public void setGoal(Goal goal) {
        this.goal = goal;
    }

    @Override
    public void clear() {
        table.clear();
    }

    @Override
    public EqualityFindTacletManager clone() {
        EqualityFindTacletManager result = new EqualityFindTacletManager();
        result.table.putAll(table);
        result.goal = goal;
        return result;
    }

}
