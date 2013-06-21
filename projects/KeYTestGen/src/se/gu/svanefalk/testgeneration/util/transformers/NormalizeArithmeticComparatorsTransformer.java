package se.gu.svanefalk.testgeneration.util.transformers;

import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;

public class NormalizeArithmeticComparatorsTransformer extends
        AbstractTermTransformer {

    private static Sort INT_SORT = new SortImpl(new Name("int"));

    private static final TermBuilder termBuilder = TermBuilder.DF;

    public static NormalizeArithmeticComparatorsTransformer getInstance(
            final Services services) {
        return new NormalizeArithmeticComparatorsTransformer(services);
    }

    private boolean sawNegation = false;

    private final Services services;

    private NormalizeArithmeticComparatorsTransformer(final Services services) {
        this.services = services;
    }

    private Term addToZValue(final Term term, final int toAdd) {

        if (TermParserTools.isInteger(term)) {
            int currentValue = 0;
            if (TermParserTools.isIntegerNegation(term.sub(0))) {
                currentValue = Integer.parseInt("-"
                        + TermParserTools.resolveNumber(term.sub(0).sub(0)));
            } else {
                currentValue = Integer.parseInt(TermParserTools.resolveNumber(term.sub(0)));
            }

            final int newValue = currentValue + toAdd;
            return NormalizeArithmeticComparatorsTransformer.termBuilder.zTerm(
                    services, Integer.toString(newValue));

        } else {
            final Term val = NormalizeArithmeticComparatorsTransformer.termBuilder.zTerm(
                    services, Integer.toString(toAdd));
            return NormalizeArithmeticComparatorsTransformer.termBuilder.add(
                    services, term, val);
        }
    }

    @Override
    public Term transform(Term term) throws TermTransformerException {

        /*
         * Put term into NNF.
         */
        term = NegationNormalFormTransformer.getInstance().transform(term);

        return transformTerm(term);
    }

    @Override
    protected Term transformBinaryFunction(final Term term)
            throws TermTransformerException {

        if (sawNegation && TermParserTools.isArithmeticComparator(term)) {

            sawNegation = false;

            final Term leftChild = transform(term.sub(0));
            final Term rightChild = transform(term.sub(1));

            /*
             * Represents the value 1.
             */
            final Term one = NormalizeArithmeticComparatorsTransformer.termBuilder.zTerm(
                    services, "1");

            if (TermParserTools.isGreaterOrEquals(term)) {

                final Term incrementedChild = NormalizeArithmeticComparatorsTransformer.termBuilder.add(
                        services, leftChild, one);

                return NormalizeArithmeticComparatorsTransformer.termBuilder.leq(
                        incrementedChild, rightChild, services);
            }

            if (TermParserTools.isLessOrEquals(term)) {

                final Term incrementedChild = NormalizeArithmeticComparatorsTransformer.termBuilder.add(
                        services, rightChild, one);

                return NormalizeArithmeticComparatorsTransformer.termBuilder.geq(
                        leftChild, incrementedChild, services);
            }

            /*
             * Negations of equalities translate to a pair of inequalities
             * around the excluded value.
             */
            if (TermParserTools.isEquals(term)) {

                final Term rhandMinusOne = addToZValue(rightChild, -1);
                final Term rhandPlusOne = addToZValue(rightChild, 1);

                final Term lessThanConstraint = NormalizeArithmeticComparatorsTransformer.termBuilder.leq(
                        leftChild, rhandMinusOne, services);
                final Term greaterThanConstraint = NormalizeArithmeticComparatorsTransformer.termBuilder.geq(
                        leftChild, rhandPlusOne, services);

                return NormalizeArithmeticComparatorsTransformer.termBuilder.or(
                        lessThanConstraint, greaterThanConstraint);
                /*
                 * Term valueMinusOne = termBuilder.add(services, rightChild,
                 * t2) Term leftInequality = termBuilder.leq( incrementedChild,
                 * rightChild, services); Term inequalities;
                 */
            }
        }

        return super.transformBinaryFunction(term);
    }

    @Override
    protected Term transformEquals(final Term term)
            throws TermTransformerException {
        if (TermParserTools.isArithmeticComparator(term)) {
            return transformBinaryFunction(term);
        } else {
            return super.transformEquals(term);
        }

    }

    @Override
    protected Term transformNot(final Term term)
            throws TermTransformerException {
        sawNegation = true;
        return transformTerm(term.sub(0));
    }
}