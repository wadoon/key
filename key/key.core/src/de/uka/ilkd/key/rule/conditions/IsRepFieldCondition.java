package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * This variable condition checks if the given field denotes a rep field.
 * @author Wolfram Pfeifer
 */
public class IsRepFieldCondition extends VariableConditionAdapter {
    /** if the condition is preceded by <code>\\not</code>*/
    private final boolean negated;

    /** the SchemaVariable (term of sort Field) to check */
    private final SchemaVariable f;

    /**
     * Creates a new IsRepFieldCondition.
     * @param f the Field SchemaVariable
     * @param negation true iff the condition is negated
     */
    public IsRepFieldCondition(final SchemaVariable f, boolean negation) {
        this.f = f;
        this.negated = negation;
        // TODO: check for correct sort of SV?
    }

    @Override
    public boolean check(SchemaVariable var, SVSubstitute instCandidate, SVInstantiations instMap,
            Services services) {

        boolean result = checkInternal(var, instCandidate, services);
        return negated ? !result : result;
    }

    // this method performs the actual check for rep field
    private boolean checkInternal(SchemaVariable var, SVSubstitute instCand, Services services) {
        if (var != f) {
            return true;
        }

        if (instCand instanceof Term) {
            Operator op = ((Term) instCand).op();
            if (op instanceof Function) {
                String name = op.name().toString();

                String className;
                String attributeName;

                // check for normal attribute
                int endOfClassName = name.indexOf("::$");
                int startAttributeName = endOfClassName + 3;

                if (endOfClassName < 0) {
                    // not a normal attribute, maybe an implicit attribute like <created>?
                    endOfClassName = name.indexOf("::<");
                    startAttributeName = endOfClassName + 2;
                }

                if (endOfClassName < 0) {
                    return false;
                }

                className     = name.substring(0, endOfClassName);
                attributeName = name.substring(startAttributeName);

                ProgramVariable attribute = services.getJavaInfo()
                        .getAttribute(attributeName, className);

                if (attribute == null) {
                    return false;
                }

                return attributeName.startsWith("rep_");
            }
        }
        return false;
    }

    @Override
    public String toString() {
        String prefix = negated ? "\\not" : "";
        return prefix + "\\isRepField(" + f + ")";
    }
}
