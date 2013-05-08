package se.gu.svanefalk.keystone;

import java.util.HashSet;
import java.util.Set;

import se.gu.svanefalk.testgeneration.keystone.util.Tuple;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;

public class Preprocessor {

    private static class VariableCollector extends DefaultVisitor {

        private final Set<ProgramVariable> variables;

        public VariableCollector(final Set<ProgramVariable> variables) {
            super();
            this.variables = variables;
        }

        @Override
        public void visit(final Term visited) {
            if (TermParserTools.isProgramVariable(visited)) {
                variables.add((ProgramVariable) visited);
            }
        }
    }

    private static Preprocessor instance = null;

    private static final int PROBLEM_PRICE = 1;

    private static final int VARIABLE_PRICE = 2;

    public static Preprocessor getInstance() {
        if (Preprocessor.instance == null) {
            Preprocessor.instance = new Preprocessor();
        }
        return Preprocessor.instance;
    }

    private Preprocessor() {
    }

    private Set<ProgramVariable> collectVariables(final Term term) {
        final Set<ProgramVariable> variableSet = new HashSet<>();
        term.execPreOrder(new VariableCollector(variableSet));
        return variableSet;
    }

    public Set<Term> createMinimalProblemSet(final Term term) {

        final Set<Term> minimalProblemSet = new HashSet<>();
        createMinimalProblemSet_helper(term, minimalProblemSet);
        return minimalProblemSet;
    }

    private void createMinimalProblemSet_helper(final Term term,
            final Set<Term> minimalProblemSet) {

        if (TermParserTools.isAnd(term)) {
            createMinimalProblemSet_helper(term.sub(0), minimalProblemSet);
            createMinimalProblemSet_helper(term.sub(1), minimalProblemSet);
        }

        if (TermParserTools.isOr(term)) {
            if (price(term.sub(0)) <= price(term.sub(1))) {
                createMinimalProblemSet_helper(term.sub(0), minimalProblemSet);
            } else {
                createMinimalProblemSet_helper(term.sub(1), minimalProblemSet);
            }
        }
    }

    private int evaluatePrice(final Tuple<Integer, Set<ProgramVariable>> tuple) {
        return tuple.getFirst() + tuple.getSecond().size();
    }

    private int price(final Term term) {
        final Tuple<Integer, Set<ProgramVariable>> priceTuple = priceGather(term);
        return priceTuple.getFirst()
                + (priceTuple.getSecond().size() * Preprocessor.VARIABLE_PRICE);
    }

    private Tuple<Integer, Set<ProgramVariable>> priceGather(final Term term) {

        if (TermParserTools.isAnd(term)) {
            final Tuple<Integer, Set<ProgramVariable>> leftTuple = priceGather(term.sub(0));
            final Tuple<Integer, Set<ProgramVariable>> rightTuple = priceGather(term.sub(1));

            final int newWeight = leftTuple.getFirst() + rightTuple.getFirst();
            final Set<ProgramVariable> newVariableSet = new HashSet<>();
            newVariableSet.addAll(leftTuple.getSecond());
            newVariableSet.addAll(leftTuple.getSecond());

            return new Tuple<Integer, Set<ProgramVariable>>(newWeight,
                    newVariableSet);
        }

        if (TermParserTools.isOr(term)) {
            final Tuple<Integer, Set<ProgramVariable>> leftTuple = priceGather(term.sub(0));
            final Tuple<Integer, Set<ProgramVariable>> rightTuple = priceGather(term.sub(1));

            if (evaluatePrice(leftTuple) <= evaluatePrice(rightTuple)) {
                return leftTuple;
            } else {
                return rightTuple;
            }
        }

        return new Tuple<Integer, Set<ProgramVariable>>(
                Preprocessor.PROBLEM_PRICE, collectVariables(term));
    }
}