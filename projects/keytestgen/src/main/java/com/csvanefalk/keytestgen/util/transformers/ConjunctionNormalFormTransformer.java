package com.csvanefalk.keytestgen.util.transformers;

import com.csvanefalk.keytestgen.util.parsers.TermParserTools;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;

/**
 * This parser is used in order to put a Term into Conjunctive Normal Form.
 * <p/>
 * Assume that a Literal <i>L</i> is either an atom p or the negation of an atom
 * !p. A Term <i>T</i> is in CNF if it is a conjunction of clauses, where each
 * clause <i>D</i> is a disjunction of literals:
 * <p/>
 * <pre>
 * L ::= p | !p
 * D ::= L | L OR D
 * C ::= D | D AND T
 * </pre>
 *
 * @author christopher
 */
public class ConjunctionNormalFormTransformer extends AbstractTermTransformer {

    private static ConjunctionNormalFormTransformer instance = null;

    /**
     * Used for putting the target term into Negation Normal Form.
     */
    private static final NegationNormalFormTransformer nnfTransformer = NegationNormalFormTransformer.getInstance();

    /**
     * Used for removing implications from the target term.
     */
    private static final RemoveImplicationsTransformer removeImplicationsTransformer = RemoveImplicationsTransformer.getInstance();

    public static ConjunctionNormalFormTransformer getInstance() {
        if (ConjunctionNormalFormTransformer.instance == null) {
            ConjunctionNormalFormTransformer.instance = new ConjunctionNormalFormTransformer();
        }
        return ConjunctionNormalFormTransformer.instance;
    }

    private ConjunctionNormalFormTransformer() {
    }

    /**
     * Implements the DISTR routine of the CNF algorithm. It is defined as
     * follows:
     * <p/>
     * <pre>
     *
     * Pre: n1 and n2 are in CNF
     * Post: DISTR(n1,n2) computes a CNF for n1 OR n2
     *
     * function DISTR(n1, n2):
     * begin function
     *     case
     *         n1 is n1-1 AND n1-2 : return DISTR(n1-1,n2) AND DISTR(n1-2,n2)
     *         n2 is n2-1 AND n2-2 : return DISTR(n1,n2-1) AND DISTR(n1,n2-2)
     *         otherwise : return n1 OR n2
     *     end case
     * end function
     *
     * </pre>
     *
     * @param firstTerm  n1
     * @param secondTerm n2
     * @return the distributed term
     */
    private Term distribute(final Term firstTerm, final Term secondTerm) {

        if (TermParserTools.isAnd(firstTerm)) {

            final Term firstDistributedChild = distribute(firstTerm.sub(0), secondTerm);
            final Term secondDistributedChild = distribute(firstTerm.sub(1), secondTerm);

            return termFactory.createTerm(Junctor.AND, firstDistributedChild, secondDistributedChild);

        } else if (TermParserTools.isAnd(secondTerm)) {

            final Term firstDistributedChild = distribute(firstTerm, secondTerm.sub(0));
            final Term secondDistributedChild = distribute(firstTerm, secondTerm.sub(1));

            return termFactory.createTerm(Junctor.AND, firstDistributedChild, secondDistributedChild);

        } else {

            return termFactory.createTerm(Junctor.OR, firstTerm, secondTerm);
        }
    }

    /**
     * Puts a Term into Conjunctive Normal Form, using the following algorithm:
     * <p/>
     * <pre>
     * Pre: x is implication free and in Negation Normal Form
     * Post: CNF(x) computes and equivalent CNF for(x)
     * function CNF(x):
     * begin function
     *     case
     *         x is a literal : return x
     *         x is x1 AND x2 : return CNF(x1) and CNF(x2)
     *         x is x1 OR x2 : return DISTR(CNF(x1) and CNF(x2))
     *     end case
     * end function
     * </pre>
     * <p/>
     * The algorithm was taken from:
     * <p/>
     * (Huth and Ryan, <i>Logic in Computer Science</i>, pages 60-61, 2nd Ed.
     * Cambridge University press, 2008)
     *
     * @param term the term to transform
     * @return the transformed term
     */
    @Override
    public Term transform(final Term term) throws TermTransformerException {

        /*
         * Remove implications from the term
         */
        final Term implicationFreeTerm = ConjunctionNormalFormTransformer.removeImplicationsTransformer.transform(term);

        /*
         * Put the term into Negation Normal Form
         */
        final Term nnfTerm = ConjunctionNormalFormTransformer.nnfTransformer.transform(implicationFreeTerm);

        return transformTerm(nnfTerm);
    }

    @Override
    protected Term transformOr(final Term term) throws TermTransformerException {

        final Term firstTransformedTerm = transformTerm(term.sub(0));
        final Term secondTransformedTerm = transformTerm(term.sub(1));
        return distribute(firstTransformedTerm, secondTransformedTerm);
    }
}