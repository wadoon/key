package de.uka.ilkd.key.testgeneration.core.parsers.transformers;

import java.util.LinkedList;
import java.util.Queue;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.testgeneration.core.parsers.TermParserException;

/**
 * A Transformer which removes {@link IfThenElse} statements from a Term,
 * replacing them with a semantically equivalent conjunction of conditions.
 * 
 * @author christopher
 * 
 */
public class RemoveIfThenElseTransformer extends AbstractTermTransformer {

    /**
     * Removes all instances of {@link IfThenElse} from a pathcondition, instead
     * replacing them with a conjunction of conditions extracted from the
     * if-then-else statement.
     * <p>
     * Primarily meant to simplify path conditions, may well have other uses.
     */
    @Override
    public Term transform(Term term) throws TermTransformerException {
        return transformTerm(term);
    }

    /**
     * If-then-else statements can be simplified only in the event that we
     * understand what their expected outcome is, from KeYs perspective. For
     * now, the only way I can see to do this is via equals statements.
     */
    @Override
    protected Term transformEquals(Term term) throws TermTransformerException {

        try {
            Term firstChild = term.sub(0);
            Term secondChild = term.sub(1);

            if (isIfThenElse(firstChild)) {

                /*
                 * The conditions which will be generated from this
                 * transformation. These will later be put encoded as a set of
                 * conjunctions.
                 */
                Queue<Term> conditions = new LinkedList<Term>();

                /*
                 * The expected outcome of the evaluation of the if-then-else
                 * statement. May be choosen arbitrarily, see below.
                 */
                boolean outcome = translateToJavaBoolean(secondChild);

                /*
                 * If the second operand is a boolean, it can only (?) be a
                 * boolean constant, or a boolean variable. If it is a constant,
                 * we set it as the expected outcome for the if-then-else
                 * statement. If it is a variable, then we instea assume true as
                 * the desired outcome, and assign true to this variable.
                 */
                if (isBoolean(secondChild)) {

                    if (isBooleanConstant(secondChild)) {
                        outcome = translateToJavaBoolean(secondChild);
                    } else {
                        outcome = true;
                        Term stuff = createTrueConstant();
                        Term newSecondChild = termFactory.createTerm(
                                Equality.EQUALS, secondChild,
                                createTrueConstant());

                        conditions.add(newSecondChild);
                    }

                    /*
                     * It is possible that the right operand may be another
                     * if-then-else statement. If this is the case, we assume
                     * true as the desired outcome of that if-else-statement
                     * (since we are free to assume any outcome), and formalize
                     * by creating and equals term for this if-then-else
                     * statement.
                     */
                } else {
                    outcome = true;
                    Term newSecondChild = termFactory.createTerm(
                            Equality.EQUALS, secondChild, createTrueConstant());

                    conditions.add(newSecondChild);
                }

                resolveIfThenElse(firstChild, outcome, conditions);
                Term newTerm = constructConjunction(conditions);

                /*
                 * Continue parsing normally
                 */
                return transformAnd(newTerm);

            } else {

                return super.transformEquals(term);
            }

        } catch (TermParserException e) {

            throw new TermTransformerException(e.getMessage());
        }

    }

    private void resolveIfThenElse(Term term, boolean expectedOutcome,
            Queue<Term> conditions) throws TermTransformerException {

        try {

            /*
             * Save the branch condition
             */
            Term condition = term.sub(0);

            /*
             * Study both the Then and Else branches, in order to determine if
             * either of them yields the desired outcome value. If neither does,
             * this means we have a nested if-then-else statement to resolve.
             */
            Term thenBranch = term.sub(1);
            Term elseBranch = term.sub(2);
            Term nestedBranch = null;
            Term conditionToSave = null;
            boolean sawEndBranch = false;
            boolean realOutcome = false;

            /*
             * Process the Then branch in the fashion described above.
             */
            if (isEndBranch(thenBranch)) {
                sawEndBranch = true;
                realOutcome = translateToJavaBoolean(thenBranch);
                if (realOutcome == expectedOutcome) {
                    conditions.add(condition);
                    return;
                } else {
                    conditionToSave = termFactory.createTerm(Junctor.NOT,
                            condition);
                }
            } else {
                nestedBranch = thenBranch;
            }

            /*
             * Process the Else branch in the same fashion.
             */
            if (isEndBranch(elseBranch)) {
                sawEndBranch = true;
                realOutcome = translateToJavaBoolean(elseBranch);
                if (realOutcome == expectedOutcome) {
                    conditions.add(termFactory.createTerm(Junctor.NOT,
                            condition));
                    return;
                } else {
                    conditionToSave = condition;
                }
            } else {
                nestedBranch = elseBranch;
            }

            /*
             * If the one or both of the end-branches did not contain the
             * expected outcome, recursively resolve the branch corresponding to
             * a nested if-then-statement.
             */
            conditions.add(conditionToSave);
            resolveIfThenElse(nestedBranch, expectedOutcome, conditions);

        } catch (TermParserException e) {

            throw new TermTransformerException(e.getMessage());
        }
    }

    private Term constructConjunction(Queue<Term> conditions) {

        if (conditions.size() == 0) {
            return null;

        } else if (conditions.size() == 1) {
            return conditions.poll();

        } else {

            Term leftChild = conditions.poll();
            Term rightChild = constructConjunction(conditions);

            return termFactory.createTerm(Junctor.AND, leftChild, rightChild);
        }
    }

    private boolean isEndBranch(Term term) {
        return !isIfThenElse(term);
    }
}
