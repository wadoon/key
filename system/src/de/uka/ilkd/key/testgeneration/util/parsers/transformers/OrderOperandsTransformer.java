package de.uka.ilkd.key.testgeneration.util.parsers.transformers;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * Transformer which rebuilds a Term in such a way that all Junctors having the
 * same operands, also have them in the same order.
 * 
 * @author christopher
 * 
 */
public class OrderOperandsTransformer extends AbstractTermTransformer {

    @Override
    public Term transform(Term term) throws TermTransformerException {

        return transformTree(term);
    }

    @Override
    protected Term transformAnd(Term term) throws TermTransformerException {

        Term transformedFirstChild = transformTerm(term.sub(0));
        Term transformedSecondChild = transformTerm(term.sub(1));

        String firstChildName = transformedFirstChild.toString();
        String secondChildName = transformedSecondChild.toString();

        int comparison = firstChildName.compareTo(secondChildName);
        if (comparison > 0) {
            return termFactory.createTerm(Junctor.AND, transformedSecondChild,
                    transformedFirstChild);
        } else {
            return termFactory.createTerm(Junctor.AND, transformedFirstChild,
                    transformedSecondChild);
        }
    }

    @Override
    protected Term transformOr(Term term) throws TermTransformerException {

        Term transformedFirstChild = transformTerm(term.sub(0));
        Term transformedSecondChild = transformTerm(term.sub(1));

        String firstChildName = transformedFirstChild.toString();
        String secondChildName = transformedSecondChild.toString();

        int comparison = firstChildName.compareTo(secondChildName);
        if (comparison > 0) {
            return termFactory.createTerm(Junctor.OR, transformedSecondChild,
                    transformedFirstChild);
        } else {
            return termFactory.createTerm(Junctor.OR, transformedFirstChild,
                    transformedSecondChild);
        }
    }

    @Override
    protected Term transformEquals(Term term) throws TermTransformerException {

        Term transformedFirstChild = transformTerm(term.sub(0));
        Term transformedSecondChild = transformTerm(term.sub(1));

        String firstChildName = transformedFirstChild.toString();
        String secondChildName = transformedSecondChild.toString();

        int comparison = firstChildName.compareTo(secondChildName);
        if (comparison > 0) {
            return termFactory.createTerm(term.op(), transformedSecondChild,
                    transformedFirstChild);
        } else {
            return termFactory.createTerm(term.op(), transformedFirstChild,
                    transformedSecondChild);
        }
    }

    private Term transformTree(Term term) {

        if (isOr(term) || isAnd(term)) {

            Map<String, Term> identifierMapping = new HashMap<String, Term>();
            PriorityQueue<String> sortedIdentifiers = new PriorityQueue<String>();
            List<Term> literals = new LinkedList<Term>();

            /*
             * For all subtrees of this term of the same sort, gather all
             * literals they have as children.
             */
            Operator operator = term.op();
            collectLiteralsFromTree(term, operator, literals);

            /*
             * Recursively transform all the gathered literals, sort their
             * identifiers, and put them into the mapping.
             */
            for (Term literal : literals) {
                Term transformedLiteral = transformTree(literal);
                String identifier = transformedLiteral.toString();

                identifierMapping.put(identifier, transformedLiteral);
                sortedIdentifiers.add(identifier);
            }

            /*
             * Construct a new tree with the transformed literals.
             */
            Term newTerm = constructTree(sortedIdentifiers, identifierMapping,
                    operator);
            return newTerm;
        } else {

            return term;
        }
    }

    private Term constructTree(PriorityQueue<String> sortedIdentifiers,
            Map<String, Term> mappings, Operator operator) {

        if (sortedIdentifiers.size() == 0) {
            return null;

        } else if (sortedIdentifiers.size() == 1) {
            return mappings.get(sortedIdentifiers.poll());

        } else {

            String leftIdentifier = sortedIdentifiers.poll();
            Term leftChild = mappings.get(leftIdentifier);
            Term rightChild = constructTree(sortedIdentifiers, mappings,
                    operator);

            return termFactory.createTerm(operator, leftChild, rightChild);
        }
    }

    private void collectLiteralsFromTree(Term term, Operator operator,
            List<Term> literals) {

        if (representsOperator(term, operator)) {
            collectLiteralsFromTree(term.sub(0), operator, literals);
            collectLiteralsFromTree(term.sub(1), operator, literals);
        } else {
            literals.add(term);
        }
    }

    private boolean representsOperator(Term term, Operator operator) {

        return term.op().name().toString().equals(operator.name().toString());
    }
}
