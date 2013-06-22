package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

/**
 * Provides a high-level representation of a comparator. Such a comparator can
 * be either a comparison between boolean expressions (i.e. a == true, where a
 * is boolean), numeric expressions (i.e. b < 3, where b is a number), or
 * references (i.e. c != null, where c is a Java object).
 * <p>
 * This abstraction does not enforce Java type safety (i.e. it is possible to
 * construct an abstraction such as 3 == false), but relies on the KeY, which
 * creates the underlying Term this abstraction is built from, in order to
 * ensure that this is already present.
 * 
 * @author christopher
 * 
 */
public class OracleComparator extends OracleExpression {

    /**
     * The types of Java comparators.
     */
    public enum ComparatorType {

        /**
         * The equals comparator.
         */
        EQUALS("=="),

        /**
         * The greater-than-or-equals comparator.
         */
        GREATER_OR_EQUALS(">="),

        /**
         * The greater-than comparator.
         */
        GREATER_THAN(">"),

        /**
         * The less-than-or-equals comparator.
         */
        LESS_OR_EQUALS("<="),

        /**
         * The less-than comparator.
         */
        LESS_THAN("<"),

        /**
         * The not-equals comparator.
         */
        NOT_EQUALS("!=");

        /**
         * The identifier for this comparator type.
         */
        private final String identifier;

        private ComparatorType(final String identifier) {
            this.identifier = identifier;
        }

        @Override
        public String toString() {
            return identifier;
        }
    }

    /**
     * The comparator type for this comparator instance.
     */
    private final ComparatorType comparator;

    /**
     * The first operand of the comparator.
     */
    private final OracleExpression firstOperand;

    /**
     * The second operand of the comparator.
     */
    private final OracleExpression secondOperand;

    /**
     * Constructs a new comparator.
     * 
     * @param comparatorType
     *            the comparator type
     * @param firstOperand
     *            the first operand
     * @param secondOperand
     *            the second operand
     */
    public OracleComparator(final ComparatorType comparatorType,
            final OracleExpression firstOperand,
            final OracleExpression secondOperand) {

        super(OracleType.BOOLEAN);
        comparator = comparatorType;
        this.firstOperand = firstOperand;
        this.secondOperand = secondOperand;
    }

    /**
     * @return the comparator type for this comparator.
     */
    public ComparatorType getComparatorType() {

        return comparator;
    }

    /**
     * @return the first operand of the comparator.
     */
    public OracleExpression getFirstOperand() {

        return firstOperand;
    }

    /**
     * @return the second operand of the comparator
     */
    public OracleExpression getSecondOperand() {

        return secondOperand;
    }

    @Override
    public String toString() {
        return firstOperand + " " + comparator + " " + secondOperand;
    }
}
