package se.gu.svanefalk.testgeneration.util.transformers;

import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;

public class NormalizeArithmeticComparatorsTransformer extends
        AbstractTermTransformer {

    public static NormalizeArithmeticComparatorsTransformer getInstance(
            Services services) {
        return new NormalizeArithmeticComparatorsTransformer(services);
    }

    private NormalizeArithmeticComparatorsTransformer(Services services) {
        this.services = services;
    }

    private static final TermBuilder termBuilder = TermBuilder.DF;

    private final Services services;

    private boolean sawNegation = false;

    @Override
    public Term transform(Term term) throws TermTransformerException {

        /*
         * Put term into NNF.
         */
        term = NegationNormalFormTransformer.getInstance().transform(term);

        return transformTerm(term);
    }

    @Override
    protected Term transformNot(Term term) throws TermTransformerException {
        sawNegation = true;
        return transformTerm(term.sub(0));
    }

    @Override
    protected Term transformBinaryFunction(Term term)
            throws TermTransformerException {

        if (sawNegation && TermParserTools.isArithmeticComparator(term)) {

            Term leftChild = transform(term.sub(0));
            Term rightChild = transform(term.sub(1));

            Term one = termBuilder.zTerm(services, "1");

            if (TermParserTools.isGreaterOrEquals(term)) {

                Term incrementedChild = termBuilder.add(services, leftChild,
                        one);

                return termBuilder.leq(incrementedChild, rightChild, services);
            }

            if (TermParserTools.isLessOrEquals(term)) {

                Term incrementedChild = termBuilder.add(services, rightChild,
                        one);

                return termBuilder.geq(leftChild, incrementedChild, services);
            }

            if (TermParserTools.isGreaterThan(term)) {

            }

            if (TermParserTools.isLessOrEquals(term)) {

            }
        }

        return super.transformBinaryFunction(term);
    }

    private static Sort INT_SORT = new SortImpl(new Name("int"));

}