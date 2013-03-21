package de.uka.ilkd.key.testgeneration.util.parsers.transformers;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.testgeneration.util.parsers.TermParserTools;

/**
 * Transformer which rebuilds a Term in such a way that all Junctors having the
 * same operands, also have them in the same order.
 * 
 * @author christopher
 * 
 */
public class OrderOperandsTransformer extends AbstractTermTransformer {

    private void collectLiteralsFromTree(final Term term,
            final Operator operator, final List<Term> literals) {

        if (this.representsOperator(term, operator)) {
            this.collectLiteralsFromTree(term.sub(0), operator, literals);
            this.collectLiteralsFromTree(term.sub(1), operator, literals);
        } else {
            literals.add(term);
        }
    }

    private Term constructTree(final PriorityQueue<String> sortedIdentifiers,
            final Map<String, Term> mappings, final Operator operator) {

        if (sortedIdentifiers.size() == 0) {
            return null;

        } else if (sortedIdentifiers.size() == 1) {
            return mappings.get(sortedIdentifiers.poll());

        } else {

            final String leftIdentifier = sortedIdentifiers.poll();
            final Term leftChild = mappings.get(leftIdentifier);
            final Term rightChild = this.constructTree(sortedIdentifiers,
                    mappings, operator);

            return this.termFactory.createTerm(operator, leftChild, rightChild);
        }
    }

    private boolean representsOperator(final Term term, final Operator operator) {

        return term.op().name().toString().equals(operator.name().toString());
    }

    @Override
    public Term transform(final Term term) throws TermTransformerException {

        return this.transformTree(term);
    }

    @Override
    protected Term transformAnd(final Term term)
            throws TermTransformerException {

        final Term transformedFirstChild = this.transformTerm(term.sub(0));
        final Term transformedSecondChild = this.transformTerm(term.sub(1));

        final String firstChildName = transformedFirstChild.toString();
        final String secondChildName = transformedSecondChild.toString();

        final int comparison = firstChildName.compareTo(secondChildName);
        if (comparison > 0) {
            return this.termFactory.createTerm(Junctor.AND,
                    transformedSecondChild, transformedFirstChild);
        } else {
            return this.termFactory.createTerm(Junctor.AND,
                    transformedFirstChild, transformedSecondChild);
        }
    }

    @Override
    protected Term transformEquals(final Term term)
            throws TermTransformerException {

        final Term transformedFirstChild = this.transformTerm(term.sub(0));
        final Term transformedSecondChild = this.transformTerm(term.sub(1));

        final String firstChildName = transformedFirstChild.toString();
        final String secondChildName = transformedSecondChild.toString();

        final int comparison = firstChildName.compareTo(secondChildName);
        if (comparison > 0) {
            return this.termFactory.createTerm(term.op(),
                    transformedSecondChild, transformedFirstChild);
        } else {
            return this.termFactory.createTerm(term.op(),
                    transformedFirstChild, transformedSecondChild);
        }
    }

    @Override
    protected Term transformOr(final Term term) throws TermTransformerException {

        final Term transformedFirstChild = this.transformTerm(term.sub(0));
        final Term transformedSecondChild = this.transformTerm(term.sub(1));

        final String firstChildName = transformedFirstChild.toString();
        final String secondChildName = transformedSecondChild.toString();

        final int comparison = firstChildName.compareTo(secondChildName);
        if (comparison > 0) {
            return this.termFactory.createTerm(Junctor.OR,
                    transformedSecondChild, transformedFirstChild);
        } else {
            return this.termFactory.createTerm(Junctor.OR,
                    transformedFirstChild, transformedSecondChild);
        }
    }

    private Term transformTree(final Term term) {

        if (TermParserTools.isOr(term) || TermParserTools.isAnd(term)) {

            final Map<String, Term> identifierMapping = new HashMap<String, Term>();
            final PriorityQueue<String> sortedIdentifiers = new PriorityQueue<String>();
            final List<Term> literals = new LinkedList<Term>();

            /*
             * For all subtrees of this term of the same sort, gather all
             * literals they have as children.
             */
            final Operator operator = term.op();
            this.collectLiteralsFromTree(term, operator, literals);

            /*
             * Recursively transform all the gathered literals, sort their
             * identifiers, and put them into the mapping.
             */
            for (final Term literal : literals) {
                final Term transformedLiteral = this.transformTree(literal);
                final String identifier = transformedLiteral.toString();

                identifierMapping.put(identifier, transformedLiteral);
                sortedIdentifiers.add(identifier);
            }

            /*
             * Construct a new tree with the transformed literals.
             */
            final Term newTerm = this.constructTree(sortedIdentifiers,
                    identifierMapping, operator);
            return newTerm;
        } else {

            return term;
        }
    }
}
