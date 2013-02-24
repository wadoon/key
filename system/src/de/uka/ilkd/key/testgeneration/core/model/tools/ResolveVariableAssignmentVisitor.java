package de.uka.ilkd.key.testgeneration.core.model.tools;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.testgeneration.StringConstants;
import de.uka.ilkd.key.testgeneration.core.model.implementation.Model;
import de.uka.ilkd.key.testgeneration.core.model.implementation.ModelVariable;
import de.uka.ilkd.key.testgeneration.core.parsers.TermParserException;
import de.uka.ilkd.key.testgeneration.core.parsers.visitors.KeYTestGenTermVisitor;

/**
 * Looks for junctors in a {@link Term}, and reflects their semantic meaning in
 * the {@link Model} corresponding to the term.
 * 
 * @author christopher
 */
class ResolveVariableAssignmentVisitor extends KeYTestGenTermVisitor {

    /**
     * Constant for separating fields in {@link SortDependingFunction}
     * instances.
     */
    private static final String SEPARATOR = StringConstants.FIELD_SEPARATOR
            .toString();

    /**
     * Flag to indicate if we have seen a Not operator.
     */
    private boolean sawNot;

    /**
     * The {@link Model} instance associated with the Term being visited.
     * Constructed separately by an instance of {@link TermToModelVisitor}.
     */
    private final Model model;

    public ResolveVariableAssignmentVisitor(Model model) {

        this.model = model;
    }

    @Override
    public void visit(Term visited) {

        if (isNot(visited)) {
            sawNot = true;
        } else if (isEquals(visited)) {
            parseEquals(visited);
            sawNot = false;
        } else if (isBinaryFunction2(visited) && sawNot) {
            sawNot = false;
        }
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
    private void parseEquals(Term term) {

        try {

            Term leftOperand = term.sub(0);
            Term rightOperand = term.sub(1);

            String leftOperandIdentifier;
            String rightOperandIdentifier;

            /*
             * Process primitive variables.
             */
            if (isPrimitiveType(leftOperand)) {

                /*
                 * If the left-hand hand is a boolean, configure it accordingly.
                 */
                if (isBoolean(leftOperand)) {

                    leftOperandIdentifier = resolveIdentifierString(
                            leftOperand, SEPARATOR);

                    /*
                     * If the right-hand operator is a boolean constant (TRUE or
                     * FALSE), we need to create a new such value and assign it
                     * to the variable.
                     */
                    if (isBooleanConstant(rightOperand)) {

                        ModelVariable modelVariable = model
                                .getVariableByReference(leftOperandIdentifier);

                        boolean value = isBooleanTrue(rightOperand);
                        value = (sawNot) ? !value : value;
                        model.add(modelVariable, value);
                    } else {
                        // Breakpoint hook - should never happen.
                        int dummy = 1;
                        dummy++;
                    }

                    /*
                     * Process reference variables.
                     */
                } else if (!sawNot) {

                    leftOperandIdentifier = resolveIdentifierString(
                            leftOperand, SEPARATOR);
                    rightOperandIdentifier = resolveIdentifierString(
                            rightOperand, SEPARATOR);

                    ModelVariable leftModelVariable = model
                            .getVariableByReference(leftOperandIdentifier);

                    ModelVariable rightModelVariable = model
                            .getVariableByReference(rightOperandIdentifier);

                    model.assignPointer(leftModelVariable, rightModelVariable);
                }
            }

        } catch (TermParserException e) {
            // Should never happen. Caught only because
            // AbstractTermParser requires it.
            return;
        }
    }
}
