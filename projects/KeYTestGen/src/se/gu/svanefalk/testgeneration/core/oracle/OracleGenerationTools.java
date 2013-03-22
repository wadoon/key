package se.gu.svanefalk.testgeneration.core.oracle;

import java.util.HashMap;
import java.util.Map;

import se.gu.svanefalk.testgeneration.StringConstants;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleComparator.ComparatorType;
import se.gu.svanefalk.testgeneration.core.oracle.abstraction.OracleType;
import de.uka.ilkd.key.logic.Term;

public class OracleGenerationTools {

    private static final Map<String, ComparatorType> comparators;
    private static final Map<String, OracleType> numericTypes;
    private static final Map<String, ComparatorType> negatedComparators;

    static {

        /*
         * Setup the comparators
         */
        comparators = new HashMap<String, ComparatorType>();
        comparators.put(StringConstants.EQUALS, ComparatorType.EQUALS);
        comparators.put(StringConstants.LESS_OR_EQUALS,
                ComparatorType.LESS_OR_EQUALS);
        comparators.put(StringConstants.LESS_THAN, ComparatorType.LESS_THAN);
        comparators.put(StringConstants.GREATER_OR_EQUALS,
                ComparatorType.GREATER_OR_EQUALS);
        comparators.put(StringConstants.GREATER_THAN,
                ComparatorType.GREATER_THAN);

        /*
         * Setup the numeric types
         */
        numericTypes = new HashMap<String, OracleType>();
        numericTypes.put(StringConstants.INTEGER, OracleType.INTEGER);
        numericTypes.put(StringConstants.BYTE, OracleType.BYTE);
        numericTypes.put(StringConstants.LONG, OracleType.LONG);
        numericTypes.put(StringConstants.FLOAT, OracleType.FLOAT);
        numericTypes.put(StringConstants.DOUBLE, OracleType.DOUBLE);
        numericTypes.put(StringConstants.BOOLEAN, OracleType.BOOLEAN);

        /*
         * Setup the negated comparators
         */
        negatedComparators = new HashMap<String, ComparatorType>();
        negatedComparators.put(StringConstants.EQUALS,
                ComparatorType.NOT_EQUALS);
        negatedComparators.put(StringConstants.LESS_OR_EQUALS,
                ComparatorType.GREATER_THAN);
        negatedComparators.put(StringConstants.LESS_THAN,
                ComparatorType.GREATER_OR_EQUALS);
        negatedComparators.put(StringConstants.GREATER_OR_EQUALS,
                ComparatorType.LESS_THAN);
        negatedComparators.put(StringConstants.GREATER_THAN,
                ComparatorType.LESS_OR_EQUALS);
    }

    public static ComparatorType getOracleComparator(Term term, boolean negated) {

        String operatorName = term.op().name().toString();

        if (negated) {
            return negatedComparators.get(operatorName);
        } else {
            return comparators.get(operatorName);
        }
    }

    public static OracleType getOracleType(Term term) {

        String typeName = term.sort().name().toString();

        OracleType type = numericTypes.get(typeName);

        /*
         * Creates a custom type in the event that the type is not present in
         * the repository.
         */
        if (type == null) {
            return null;
        }

        return type;
    }
}
