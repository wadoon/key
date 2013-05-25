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

            final Term leftChild = transform(term.sub(0));
            final Term rightChild = transform(term.sub(1));

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

            if (TermParserTools.isGreaterThan(term)) {

            }

            if (TermParserTools.isLessOrEquals(term)) {

            }
        }

        return super.transformBinaryFunction(term);
    }

    @Override
    protected Term transformNot(final Term term)
            throws TermTransformerException {
        sawNegation = true;
        return transformTerm(term.sub(0));
    }

}