package de.uka.ilkd.key.logic.label;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * Label attached to the modality of the validity branch of a block contract.
 *
 * @param exceptionVariable The name of the exception variable to distinguish normal from exceptional termination.
 */
public record BlockContractValidityTermLabel(ProgramVariable exceptionVariable) implements TermLabel {
    /**
     * The unique name of this label.
     */
    public static final Name NAME = new Name("BC");

    /**
     * {@inheritDoc}
     */
    public String toString() {
        return NAME + "(" + exceptionVariable() + ")";
    }

    /**
     * retrieves the original exception variable as found in the local variable declaration
     * statement
     *
     * @return the original exception variable
     */
    @Override
    public ProgramVariable exceptionVariable() {
        return exceptionVariable;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ProgramVariable getChild(int i) {
        if (i == 0) {
            return exceptionVariable();
        }
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int getChildCount() {
        return 1;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public Name name() {
        return NAME;
    }

}
