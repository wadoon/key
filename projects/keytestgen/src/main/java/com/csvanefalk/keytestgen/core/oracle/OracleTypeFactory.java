package com.csvanefalk.keytestgen.core.oracle;

import com.csvanefalk.keytestgen.StringConstants;
import com.csvanefalk.keytestgen.core.oracle.abstraction.OracleComparator.ComparatorType;
import com.csvanefalk.keytestgen.core.oracle.abstraction.OracleQuantifier.QuantifierType;
import com.csvanefalk.keytestgen.core.oracle.abstraction.OracleType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

import java.util.HashMap;
import java.util.Map;

/**
 * Factory singleton used for constructing instances of the various types
 * present in an Oracle.
 *
 * @author christopher
 */
public class OracleTypeFactory {

    /**
     * The {@link ComparatorType} instances.
     */
    private static final Map<String, ComparatorType> comparators;

    /**
     * The negations of the {@link ComparatorType} instances.
     */
    private static final Map<String, ComparatorType> negatedComparators;

    /**
     * The default primitive numeric types.
     */
    private static final Map<String, OracleType> numericTypes;

    /**
     * The {@link QuantifierType} instances.
     */
    private static final Map<String, QuantifierType> quantifiers;

    static {

        /*
         * Setup the comparators
         */
        comparators = new HashMap<String, ComparatorType>();
        OracleTypeFactory.comparators.put(StringConstants.EQUALS,
                ComparatorType.EQUALS);
        OracleTypeFactory.comparators.put(StringConstants.LESS_OR_EQUALS,
                ComparatorType.LESS_OR_EQUALS);
        OracleTypeFactory.comparators.put(StringConstants.LESS_THAN,
                ComparatorType.LESS_THAN);
        OracleTypeFactory.comparators.put(StringConstants.GREATER_OR_EQUALS,
                ComparatorType.GREATER_OR_EQUALS);
        OracleTypeFactory.comparators.put(StringConstants.GREATER_THAN,
                ComparatorType.GREATER_THAN);

        /*
         * Setup the numeric types
         */
        numericTypes = new HashMap<String, OracleType>();
        OracleTypeFactory.numericTypes.put(StringConstants.INTEGER,
                OracleType.INTEGER);
        OracleTypeFactory.numericTypes.put(StringConstants.BYTE,
                OracleType.BYTE);
        OracleTypeFactory.numericTypes.put(StringConstants.LONG,
                OracleType.LONG);
        OracleTypeFactory.numericTypes.put(StringConstants.FLOAT,
                OracleType.FLOAT);
        OracleTypeFactory.numericTypes.put(StringConstants.DOUBLE,
                OracleType.DOUBLE);
        OracleTypeFactory.numericTypes.put(StringConstants.BOOLEAN,
                OracleType.BOOLEAN);

        /*
         * Setup the negated comparators
         */
        negatedComparators = new HashMap<String, ComparatorType>();
        OracleTypeFactory.negatedComparators.put(StringConstants.EQUALS,
                ComparatorType.NOT_EQUALS);
        OracleTypeFactory.negatedComparators.put(
                StringConstants.LESS_OR_EQUALS, ComparatorType.GREATER_THAN);
        OracleTypeFactory.negatedComparators.put(StringConstants.LESS_THAN,
                ComparatorType.GREATER_OR_EQUALS);
        OracleTypeFactory.negatedComparators.put(
                StringConstants.GREATER_OR_EQUALS, ComparatorType.LESS_THAN);
        OracleTypeFactory.negatedComparators.put(StringConstants.GREATER_THAN,
                ComparatorType.LESS_OR_EQUALS);

        /*
         * Setup the quantifiers
         */
        quantifiers = new HashMap<String, QuantifierType>();
        OracleTypeFactory.quantifiers.put(StringConstants.FORALL,
                QuantifierType.FORALL);
        OracleTypeFactory.quantifiers.put(StringConstants.EXISTS,
                QuantifierType.EXISTS);
    }

    /**
     * Constructs a {@link ComparatorType} instance corresponding to a given
     * {@link Term}.
     *
     * @param term    the term
     * @param negated flag to indicat whether the comparator should be negated.
     * @return the comparator
     * @throws OracleGeneratorException
     */
    public static ComparatorType getComparatorType(final Term term,
                                                   final boolean negated) throws OracleGeneratorException {

        final String operatorName = term.op().name().toString();

        ComparatorType comparatorType = null;

        if (negated) {
            comparatorType = OracleTypeFactory.negatedComparators.get(operatorName);
        } else {
            comparatorType = OracleTypeFactory.comparators.get(operatorName);
        }

        if (comparatorType == null) {
            throw new OracleGeneratorException(
                    "Could not construct comparator type: found "
                            + operatorName);
        } else {
            return comparatorType;
        }
    }

    /**
     * Creates an {@link OracleType} for a a {@link QuantifiableVariable}
     * instance. This is functionally identical to {@link #getOracleType(Term)},
     * and exsits to deal with the special case (syntactically speaking) of
     * these variables.
     *
     * @param quantifiableVariable the variable
     * @return the corresponding type
     */
    public static OracleType getOracleType(
            final QuantifiableVariable quantifiableVariable) {

        final String typeName = quantifiableVariable.sort().name().toString();

        final int lastDelimiter = typeName.lastIndexOf('.');

        if (lastDelimiter == -1) {
            return new OracleType(typeName, typeName);
        } else {
            final String shortName = typeName.substring(lastDelimiter + 1);
            return new OracleType(shortName, typeName);
        }
    }

    /**
     * Constructs an {@link OracleType} instance corresponding to the type of a
     * given {@link Term}.
     *
     * @param term the term
     * @return the corresponding type
     */
    public static OracleType getOracleType(final Term term) {

        final String typeName = term.sort().name().toString();

        OracleType type = OracleTypeFactory.numericTypes.get(typeName);

        /*
         * Creates a custom type in the event that the type is not present in
         * the repository.
         */
        if (type == null) {

            final int lastDelimiter = typeName.lastIndexOf('.');

            if (lastDelimiter == -1) {
                type = new OracleType(typeName, typeName);
            } else {
                final String shortName = typeName.substring(lastDelimiter);
                type = new OracleType(shortName, typeName);
            }
        }
        return type;
    }

    /**
     * Construct a {@link QuantifierType} instance corresponding to a given
     * {@link Term} representing the same construct.
     *
     * @param term the term
     * @return the quantifier type
     * @throws OracleGeneratorException
     */
    public static QuantifierType getQuantifierType(final Term term)
            throws OracleGeneratorException {
        final String operatorName = term.op().name().toString();

        final QuantifierType type = OracleTypeFactory.quantifiers.get(operatorName);

        if (type == null) {
            throw new OracleGeneratorException(
                    "Could not construct quantifier type: found "
                            + operatorName);
        } else {

            return type;
        }
    }
}
