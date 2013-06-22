package se.gu.svanefalk.testgeneration.core.codecoverage.implementation;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.expression.operator.ComparativeOperator;
import de.uka.ilkd.key.logic.op.ProgramVariable;

public class LogicConditionExtractor {

    private static LogicConditionExtractor instance = null;

    public static LogicConditionExtractor getInstance() {
        if (LogicConditionExtractor.instance == null) {
            LogicConditionExtractor.instance = new LogicConditionExtractor();
        }
        return LogicConditionExtractor.instance;
    }

    private LogicConditionExtractor() {

    }

    public Set<ProgramElement> getConditions(final Expression expression) {

        final Set<ProgramElement> returnSet = new HashSet<ProgramElement>();
        getConditionsHelper(expression, returnSet);
        return returnSet;
    }

    private void getConditionsHelper(final ProgramElement element,
            final Set<ProgramElement> returnSet) {

        if (element instanceof Operator) {

            if (element instanceof ComparativeOperator) {
                returnSet.add(element);

            } else {
                final Operator operator = (Operator) element;
                for (int i = 0; i < operator.getChildCount(); i++) {
                    getConditionsHelper(operator.getChildAt(i), returnSet);
                }
            }
        }

        if (element instanceof ProgramVariable) {
            returnSet.add(element);
        }
    }
}
