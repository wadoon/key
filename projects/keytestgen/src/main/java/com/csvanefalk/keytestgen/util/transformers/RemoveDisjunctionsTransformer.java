package com.csvanefalk.keytestgen.util.transformers;

import com.csvanefalk.keytestgen.keystone.util.Tuple;
import com.csvanefalk.keytestgen.util.parsers.TermParserTools;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import java.util.HashSet;
import java.util.Set;

/**
 * This transformer eliminates all disjunctions from a Term.
 * <p/>
 * Each disjunctive statement is analyzed in order to choose the "simplest" of
 * its operands, which is then used to replace the disjunction as a whole. As
 * such, the transformer also performs some rudimentary optimization, turning
 * the Term into an equivalent form which is easier to solve.
 *
 * @author christopher
 */
public class RemoveDisjunctionsTransformer extends AbstractTermTransformer {

    private static RemoveDisjunctionsTransformer instance = null;

    public static RemoveDisjunctionsTransformer getInstance() {
        if (RemoveDisjunctionsTransformer.instance == null) {
            RemoveDisjunctionsTransformer.instance = new RemoveDisjunctionsTransformer();
        }
        return RemoveDisjunctionsTransformer.instance;
    }

    private RemoveDisjunctionsTransformer() {
    }

    private static final int PROBLEM_PRICE = 1;
    private static final int VARIABLE_PRICE = 2;

    @Override
    public Term transform(Term term) throws TermTransformerException {
        return transformTerm(term);
    }

    /**
     * If a disjunction is encountered, return the sub-tree with the smaller
     * price.
     *
     * @see RemoveDisjunctionsTransformer#price(Term)
     */
    @Override
    protected Term transformOr(Term term) throws TermTransformerException {

        Term firstChild = term.sub(0);
        Term secondChild = term.sub(1);

        int firstPrice = price(term.sub(0));
        int secondPrice = price(term.sub(1));

        return firstPrice < secondPrice ? firstChild : secondChild;
    }

    private int weightTerm(final Tuple<Integer, Set<ProgramVariable>> tuple) {
        return tuple.getFirst() + tuple.getSecond().size();
    }

    /**
     * Prices a given term. The "price" of the term is a function of the number
     * of unique variables and number of logical operations occuring in it.
     * <p/>
     * TODO: This algorithm is very primitive, and could be improved.
     *
     * @param term the term
     * @return the price of the term
     */
    private int price(final Term term) {
        final Tuple<Integer, Set<ProgramVariable>> priceTuple = priceGather(term);
        return priceTuple.getFirst() + (priceTuple.getSecond().size() * VARIABLE_PRICE);
    }

    /**
     * Gathers metadata for the purpose of pricing a given term. Such metadata
     * includes the number of unique variables occuring in the term, as well as
     * the number of individual operations occuring in it.
     *
     * @param term the term
     * @return the pricing metadata
     */
    private Tuple<Integer, Set<ProgramVariable>> priceGather(final Term term) {

        /*
         * If a conjunction is encountered, price both operands, and create a
         * total price by combining these two prices.
         */
        if (TermParserTools.isAnd(term)) {
            final Tuple<Integer, Set<ProgramVariable>> leftTuple = priceGather(term.sub(0));
            final Tuple<Integer, Set<ProgramVariable>> rightTuple = priceGather(term.sub(1));

            final int newWeight = leftTuple.getFirst() + rightTuple.getFirst();
            final Set<ProgramVariable> newVariableSet = new HashSet<ProgramVariable>();
            newVariableSet.addAll(leftTuple.getSecond());
            newVariableSet.addAll(leftTuple.getSecond());
            return new Tuple<Integer, Set<ProgramVariable>>(newWeight, newVariableSet);
        }

        /*
         * If a disjunction is encountered, return the lesser of the prices for
         * both operands.
         */
        if (TermParserTools.isOr(term)) {
            final Tuple<Integer, Set<ProgramVariable>> leftTuple = priceGather(term.sub(0));
            final Tuple<Integer, Set<ProgramVariable>> rightTuple = priceGather(term.sub(1));

            if (weightTerm(leftTuple) <= weightTerm(rightTuple)) {
                return leftTuple;
            } else {
                return rightTuple;
            }
        }

        if (TermParserTools.isNot(term)) {
            return priceGather(term.sub(0));
        }

        return new Tuple<Integer, Set<ProgramVariable>>(PROBLEM_PRICE, collectVariables(term));
    }

    /**
     * Collects all the variables present in a {@link Term} instance.
     *
     * @param term the term
     * @return the set of variables in the term
     */
    private Set<ProgramVariable> collectVariables(final Term term) {
        final Set<ProgramVariable> variableSet = new HashSet<ProgramVariable>();
        term.execPreOrder(new VariableCollector(variableSet));
        return variableSet;
    }

    private class VariableCollector extends DefaultVisitor {

        private final Set<ProgramVariable> variables;

        public VariableCollector(final Set<ProgramVariable> variables) {
            super();
            this.variables = variables;
        }

        @Override
        public void visit(final Term visited) {
            if (TermParserTools.isProgramVariable(visited)) {
                variables.add((ProgramVariable) visited.op());
            }
        }
    }
}