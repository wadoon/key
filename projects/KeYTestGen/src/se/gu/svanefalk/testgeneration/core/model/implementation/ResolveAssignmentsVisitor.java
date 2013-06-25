package se.gu.svanefalk.testgeneration.core.model.implementation;

import se.gu.svanefalk.testgeneration.StringConstants;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserException;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import se.gu.svanefalk.testgeneration.util.visitors.KeYTestGenTermVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SortDependingFunction;

/**
 * Looks for junctors in a {@link Term}, and reflects their semantic meaning in
 * the {@link Model} corresponding to the term.
 * 
 * @author christopher
 */
class ResolveAssignmentsVisitor extends KeYTestGenTermVisitor {

    /**
     * Constant for separating fields in {@link SortDependingFunction}
     * instances.
     */
    private static final String SEPARATOR = StringConstants.FIELD_SEPARATOR.toString();

    /**
     * The {@link Model} instance associated with the Term being visited.
     * Constructed separately by an instance of {@link TermToModelVisitor}.
     */
    private final Model model;

    /**
     * Flag to indicate if we have seen a Not operator.
     */
    private boolean sawNot;

    public ResolveAssignmentsVisitor(final Model model) {

        this.model = model;
    }

    /**
     * Equality has to be dealt with depending on the type of the
     * <strong>left-hand</strong> variable, since this is the operand which will
     * determine the meaning of the equality.
     * <p>
     * If the variable is <strong>primitve</strong>, equality, in our
     * abstraction, implies a value assignment: equals(a,b) simply means that
     * the value of b is copied into a. For Integer types, there is no need to
     * do this explicitly, since the SMT interface will be taking care of this,
     * and we would thus only be performing the same work twice. For Boolean
     * types, however, which are not resolved by the SMT interface, we do this
     * explicitly.
     * <p>
     * If the variable is a <strong>reference</strong> type, things get more
     * interesting, since equality in this case implies that the operands are
     * pointing to a common object in memory. To represent this in our
     * abstraction, we need to cross-reference to Value property of both
     * operands, making them point to each other. We do this by making sure that
     * whatever Value is assigned to both operands has the same unique
     * identifier.
     * 
     * @param term
     *            the term to process
     */
    private void parseEquals(final Term term) {

        try {

            final Term leftOperand = term.sub(0);
            final Term rightOperand = term.sub(1);

            String leftOperandIdentifier;
            String rightOperandIdentifier;

            /*
             * Process primitive variables.
             */
            if (TermParserTools.isPrimitiveType(leftOperand)) {

                /*
                 * If the left-hand hand is a boolean, configure it accordingly.
                 */
                if (TermParserTools.isBoolean(leftOperand)) {

                    leftOperandIdentifier = TermParserTools.resolveIdentifierString(
                            leftOperand, ResolveAssignmentsVisitor.SEPARATOR);

                    /*
                     * If the right-hand operator is a boolean constant (TRUE or
                     * FALSE), we need to create a new such value and assign it
                     * to the variable.
                     */
                    if (TermParserTools.isBooleanConstant(rightOperand)) {

                        final ModelVariable modelVariable = model.getVariable(leftOperandIdentifier);

                        boolean value = TermParserTools.isBooleanTrue(rightOperand);
                        value = sawNot ? !value : value;
                        model.add(modelVariable, value);
                    }
                }
            }

            /*
             * Process reference variables.
             */
            else if (!sawNot) {

                leftOperandIdentifier = TermParserTools.resolveIdentifierString(
                        leftOperand, ResolveAssignmentsVisitor.SEPARATOR);
                rightOperandIdentifier = TermParserTools.resolveIdentifierString(
                        rightOperand, ResolveAssignmentsVisitor.SEPARATOR);

                final ModelVariable leftModelVariable = model.getVariable(leftOperandIdentifier);
                final ModelVariable rightModelVariable = model.getVariable(rightOperandIdentifier);

                model.assignPointer(leftModelVariable, rightModelVariable);
            }

            /*
             * For not-null constraints, simply create a default instance
             */
            else if (sawNot && TermParserTools.isNullSort(rightOperand)) {

                leftOperandIdentifier = TermParserTools.resolveIdentifierString(
                        leftOperand, ResolveAssignmentsVisitor.SEPARATOR);

                final ModelVariable leftModelVariable = model.getVariable(leftOperandIdentifier);

                /*
                 * Check if the variable already has a set instance. Create one
                 * if it does not.
                 */
                if (leftModelVariable.getValue() == null) {
                    leftModelVariable.setValue(ModelInstance.constructModelInstance(leftModelVariable.getType()));
                }
            }

            /*
             * for non-equality between existing references, simply move on.
             */
            else {
                ;
            }

        } catch (final TermParserException e) {
            // Should never happen. Caught only because
            // TermParserTools requires it.
            return;
        }
    }

    @Override
    public void visit(final Term visited) {

        if (TermParserTools.isNot(visited)) {
            sawNot = true;
        } else if (TermParserTools.isEquals(visited)) {
            parseEquals(visited);
            sawNot = false;
        } else if (TermParserTools.isBinaryFunction2(visited) && sawNot) {
            sawNot = false;
        }
    }
}
