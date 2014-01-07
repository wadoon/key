package com.csvanefalk.keytestgen.util.transformers;

import com.csvanefalk.keytestgen.util.parsers.TermParserTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;

public class NormalizeArithmeticComparatorsTransformer extends AbstractTermTransformer {

    private static Sort INT_SORT = new SortImpl(new Name("int"));

    private static final TermBuilder termBuilder = TermBuilder.DF;

    public static NormalizeArithmeticComparatorsTransformer getInstance(final Services services) {
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
                currentValue = Integer.parseInt("-" + TermParserTools.resolveNumber(term.sub(0).sub(0)));
            } else {
                currentValue = Integer.parseInt(TermParserTools.resolveNumber(term.sub(0)));
            }

            final int newValue = currentValue + toAdd;
            return NormalizeArithmeticComparatorsTransformer.termBuilder.zTerm(services, Integer.toString(newValue));

        } else {
            final Term val = NormalizeArithmeticComparatorsTransformer.termBuilder
                                                                      .zTerm(services, Integer.toString(toAdd));
            return NormalizeArithmeticComparatorsTransformer.termBuilder.add(services, term, val);
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
    protected Term transformBinaryFunction(final Term term) throws TermTransformerException {

        if (TermParserTools.isArithmeticComparator(term)) {

            final Term leftChild = transform(term.sub(0));
            final Term rightChild = transform(term.sub(1));

            // Represents the value 1
            final Term one = NormalizeArithmeticComparatorsTransformer.termBuilder.zTerm(services, "1");

            if (sawNegation) {
                sawNegation = false;

                /*
                 * The negation of a x >= y is x + 1 <= y.
                 */
                if (TermParserTools.isGreaterOrEquals(term)) {

                    final Term incrementedChild = NormalizeArithmeticComparatorsTransformer.termBuilder
                                                                                           .add(services,
                                                                                                leftChild,
                                                                                                one);

                    return NormalizeArithmeticComparatorsTransformer.termBuilder
                                                                    .leq(incrementedChild, rightChild, services);
                }

                /*
                 * The negation of a x <= y is x >= y + 1.
                 */
                if (TermParserTools.isLessOrEquals(term)) {

                    final Term incrementedChild = NormalizeArithmeticComparatorsTransformer.termBuilder
                                                                                           .add(services,
                                                                                                rightChild,
                                                                                                one);

                    return NormalizeArithmeticComparatorsTransformer.termBuilder
                                                                    .geq(leftChild, incrementedChild, services);
                }

                /*
                 * The negation of a x < y is x >= y.
                 */
                if (TermParserTools.isLessThan(term)) {
                    return NormalizeArithmeticComparatorsTransformer.termBuilder.geq(leftChild, rightChild, services);
                }

                /*
                 * The negation of a x > y is x <= y.
                 */
                if (TermParserTools.isGreaterThan(term)) {
                    return NormalizeArithmeticComparatorsTransformer.termBuilder.leq(leftChild, rightChild, services);
                }

                /*
                 * Negations of equalities translate to a pair of inequalities around the excluded value.
                 * For example, the negation of x==y is (x + 1 <= y) || (x >= y + 1).
                 */
                if (TermParserTools.isEquals(term)) {

                    final Term lhandPlusOne = addToZValue(leftChild, 1);
                    final Term rhandPlusOne = addToZValue(rightChild, 1);

                    final Term lessThanConstraint = NormalizeArithmeticComparatorsTransformer.termBuilder
                                                                                             .leq(lhandPlusOne,
                                                                                                  rightChild,
                                                                                                  services);

                    final Term greaterThanConstraint = NormalizeArithmeticComparatorsTransformer.termBuilder
                                                                                                .geq(leftChild,
                                                                                                     rhandPlusOne,
                                                                                                     services);

                    return NormalizeArithmeticComparatorsTransformer.termBuilder
                                                                    .or(lessThanConstraint, greaterThanConstraint);
                }
            }

            /*
             * If there is nothing to negate, simply transform less-than and greater-then inequalities
             * into equivalent less-or-equals and greater-or-equals inequalities.
             */
            else {

                /*
                 * x < y is equivalent to x + 1 <= y.
                 */
                if (TermParserTools.isLessThan(term)) {

                    final Term incrementedChild = NormalizeArithmeticComparatorsTransformer.termBuilder
                                                                                           .add(services,
                                                                                                leftChild,
                                                                                                one);

                    return NormalizeArithmeticComparatorsTransformer.termBuilder
                                                                    .leq(incrementedChild, rightChild, services);
                }

                /*
                 * x > y is equivalent to x >= y + 1.
                 */
                if (TermParserTools.isGreaterThan(term)) {

                    final Term incrementedChild = NormalizeArithmeticComparatorsTransformer.termBuilder
                                                                                           .add(services,
                                                                                                rightChild,
                                                                                                one);

                    return NormalizeArithmeticComparatorsTransformer.termBuilder
                                                                    .geq(leftChild, incrementedChild, services);
                }
            }
        }

        return super.transformBinaryFunction(term);
    }

    @Override
    protected Term transformEquals(final Term term) throws TermTransformerException {
        if (TermParserTools.isArithmeticComparator(term)) {
            return transformBinaryFunction(term);
        } else {
            return super.transformEquals(term);
        }

    }

    @Override
    protected Term transformNot(final Term term) throws TermTransformerException {
        sawNegation = true;
        return transformTerm(term.sub(0));
    }
}