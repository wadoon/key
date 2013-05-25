package se.gu.svanefalk.testgeneration.util.transformers;

import java.util.LinkedList;
import java.util.Queue;

import se.gu.svanefalk.testgeneration.util.parsers.TermParserException;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;

/**
 * A Transformer which removes {@link IfThenElse} assertions from a Term,
 * replacing them with a semantically equivalent conjunction of conditions.
 * 
 * @author christopher
 * 
 */
public class RemoveIfThenElseTransformer extends AbstractTermTransformer {

    private static RemoveIfThenElseTransformer instance = null;

    public static RemoveIfThenElseTransformer getInstance() {
        if (RemoveIfThenElseTransformer.instance == null) {
            RemoveIfThenElseTransformer.instance = new RemoveIfThenElseTransformer();
        }
        return RemoveIfThenElseTransformer.instance;
    }

    private RemoveIfThenElseTransformer() {
    }

    private Term constructConjunction(final Queue<Term> conditions) {

        if (conditions.size() == 0) {
            return null;

        } else if (conditions.size() == 1) {
            return conditions.poll();

        } else {

            final Term leftChild = conditions.poll();
            final Term rightChild = constructConjunction(conditions);

            return termFactory.createTerm(Junctor.AND, leftChild, rightChild);
        }
    }

    private boolean isEndBranch(final Term term) {
        return !TermParserTools.isIfThenElse(term);
    }

    private void resolveIfThenElse(final Term term,
            final boolean expectedOutcome, final Queue<Term> conditions)
            throws TermTransformerException {

        try {

            /*
             * Save the branch condition
             */
            final Term condition = term.sub(0);

            /*
             * Study both the Then and Else branches, in order to determine if
             * either of them yields the desired outcome value. If neither does,
             * this means we have a nested if-then-else statement to resolve.
             */
            final Term thenBranch = term.sub(1);
            final Term elseBranch = term.sub(2);
            Term nestedBranch = null;
            Term conditionToSave = null;
            boolean realOutcome = false;

            /*
             * Process the Then branch in the fashion described above.
             */
            if (isEndBranch(thenBranch)) {
                realOutcome = TermParserTools.translateToJavaBoolean(thenBranch);
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
                realOutcome = TermParserTools.translateToJavaBoolean(elseBranch);
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

        } catch (final TermParserException e) {

            throw new TermTransformerException(e.getMessage());
        }
    }

    /**
     * Removes all instances of {@link IfThenElse} from a pathcondition, instead
     * replacing them with a conjunction of conditions extracted from the
     * if-then-else statement.
     * <p>
     * Primarily meant to simplify path conditions, may well have other uses.
     */
    @Override
    public Term transform(final Term term) throws TermTransformerException {
        return transformTerm(term);
    }

    /**
     * If-then-else assertions can be simplified only in the event that we
     * understand what their expected outcome is, from KeYs perspective. For
     * now, the only way I can see to do this is via equals assertions.
     */
    @Override
    protected Term transformEquals(final Term term)
            throws TermTransformerException {

        try {
            final Term firstChild = term.sub(0);
            final Term secondChild = term.sub(1);

            if (TermParserTools.isIfThenElse(firstChild)) {

                /*
                 * The conditions which will be generated from this
                 * transformation. These will later be put encoded as a set of
                 * conjunctions.
                 */
                final Queue<Term> conditions = new LinkedList<Term>();

                /*
                 * The expected outcome of the evaluation of the if-then-else
                 * statement. May be choosen arbitrarily, see below.
                 */
                boolean outcome = TermParserTools.translateToJavaBoolean(secondChild);

                /*
                 * If the second operand is a boolean, it can only (?) be a
                 * boolean constant, or a boolean variable. If it is a constant,
                 * we set it as the expected outcome for the if-then-else
                 * statement. If it is a variable, then we instea assume true as
                 * the desired outcome, and assign true to this variable.
                 */
                if (TermParserTools.isBoolean(secondChild)) {

                    if (TermParserTools.isBooleanConstant(secondChild)) {
                        outcome = TermParserTools.translateToJavaBoolean(secondChild);
                    } else {
                        outcome = true;
                        createTrueConstant();
                        final Term newSecondChild = termFactory.createTerm(
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
                    final Term newSecondChild = termFactory.createTerm(
                            Equality.EQUALS, secondChild, createTrueConstant());

                    conditions.add(newSecondChild);
                }

                resolveIfThenElse(firstChild, outcome, conditions);
                final Term newTerm = constructConjunction(conditions);

                /*
                 * Continue parsing normally FIXME: Contains bug, see separate
                 * test case
                 */
                return transformAnd(newTerm);

            } else {

                return super.transformEquals(term);
            }

        } catch (final TermParserException e) {

            throw new TermTransformerException(e.getMessage());
        }

    }
}
