package de.uka.ilkd.key.testgeneration.parsers;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IfExThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.NullSort;

/**
 * This class provides a lightweight framework for implementing {@link Term}
 * parsers intended to transform Terms.
 * <p>
 * This class does NOT currently contain functionality to transform all forms of
 * Terms, since it is primarily meant to be used by KeYTestGen, which only uses
 * a subset of such terms. As need dictates, this may change to support all
 * sorts of Term trees.
 * 
 * @author christopher
 * 
 */
public abstract class AbstractTermTransformer extends AbstractTermParser {

    /**
     * Used for constructing new {@link Term} instances.
     */
    protected final TermFactory termFactory = TermFactory.DEFAULT;

    /**
     * The top level function for transforming a {@link Term} instance. This
     * function will do a preliminary check to see whether the top-level
     * operator of the Term is a basic {@link Operator} or a
     * {@link SortedOperator}, and proceed with parsing from there.
     * 
     * @param term
     * @return
     */
    public Term transformTerm(Term term) throws TermTransformerException {

        /*
         * Order matters here, since SortedOperator is a subclass of Operator.
         */
        if (isSortedOperator(term)) {
            return transformSortedOperator(term);

        } else if (isIfExThenElse(term)) {
            return transformIfExThenElse(term);

        } else if (isIfThenElse(term)) {
            return transformIfThenElse(term);

        }

        throw new TermTransformerException("Unsupported SortedOperator: "
                + term.op().name());
    }

    /**
     * Transforms a {@link Term} which represents an {@link IfExThenElse}
     * structure (i.e. its {@link Operator} is of this type).
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected Term transformIfExThenElse(Term term) {

        return term;
    }

    /**
     * Transforms a {@link Term} which represents an {@link IfThenElse}
     * structure (i.e. its {@link Operator} is of this type).
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected Term transformIfThenElse(Term term) {

        return term;
    }

    /**
     * Transforms a {@link Term} which represents some kind of
     * {@link SortedOperator}.
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected Term transformSortedOperator(Term term)
            throws TermTransformerException {

        if (isFunction(term)) {
            return transformFunction(term);
        }

        if (isEquals(term)) {
            return transformEquals(term);
        }

        if (isJunctor(term)) {
            return transformJunctor(term);
        }

        if (isProgramVariable(term)) {
            return transformProgramVariable(term);
        }

        throw new TermTransformerException("Unsupported SortedOperator: "
                + term.op().name());
    }

    /**
     * Transforms a {@link Term} which represents a {@link ProgramVariable}
     * structure (i.e. its {@link Operator} is of this type).
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected Term transformProgramVariable(Term term)
            throws TermTransformerException {

        if (isLocationVariable(term)) {
            return transformLocationVariable(term);
        }

        throw new TermTransformerException("Unsupported SortedOperator: "
                + term.op().name());
    }

    /**
     * Transforms a {@link Term} which represents an {@link LocationVariable}
     * structure (i.e. its {@link Operator} is of this type).
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected Term transformLocationVariable(Term term) {

        return term;
    }

    /**
     * Transforms a {@link Term} which represents some instance of a
     * {@link Function}.
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected Term transformFunction(Term term) throws TermTransformerException {

        /*
         * Order is crucial for proper resolution here, as the precise,
         * legitimate parent-child relationships between various Function-type
         * terms are not excplicitly spelled out in terms of type relationships.
         */
        if (isNullSort(term)) {
            return transformNull(term);
        }

        if (isSortDependingFunction(term)) {
            return transformSortDependentFunction(term);
        }

        if (isBinaryFunction(term)) {
            return transformBinaryFunction(term);
        }

        if (isUnaryFunction(term)) {
            return transformUnaryFunction(term);
        }

        if (isLiteral(term)) {
            return transformLiteral(term);
        }

        if (isObserverFunction(term)) {
            return transformObserverFunction(term);

        }

        throw new TermTransformerException("Unsupported Function: "
                + term.op().name());
    }

    /**
     * Transforms a {@link Term} which represents a null element, i.e. it has
     * the sort {@link NullSort}.
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected Term transformNull(Term term) {

        return term;
    }

    private Term transformUnaryFunction(Term term)
            throws TermTransformerException {

        Term child = transformTerm(term.sub(0));

        Term newTerm = termFactory.createTerm(term.op(), child);

        return newTerm;
    }

    /**
     * Transforms a {@link Term} which represents a binary comparator. Such
     * functions include GreaterOrEquals, GreaterThan, LessOrEquals, and
     * LessThan. These are no explicitly defined as KeY operators, and are as
     * such recognized by their sorts.
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected Term transformBinaryFunction(Term term)
            throws TermTransformerException {

        Term firstChild = transformTerm(term.sub(0));
        Term secondChild = transformTerm(term.sub(1));

        Term newTerm = termFactory.createTerm(term.op(), firstChild,
                secondChild);

        return newTerm;
    }

    protected Term transformLiteral(Term term) throws TermTransformerException {

        /*
         * Literals may or may not declare children, such as 1(#);
         */
        if (!term.subs().isEmpty()) {
            Term child = transformTerm(term.sub(0));
            return termFactory.createTerm(term.op(), child);
        } else {
            return term;
        }
    }

    /**
     * Transforms a {@link Term} which represents an
     * {@link SortDependingFunction} structure (i.e. its {@link Operator} is of
     * this type).
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected Term transformSortDependentFunction(Term term) {

        return term;
    }

    protected Term transformObserverFunction(Term term) {

        if (isProgramMethod(term)) {
            return transformProgramMethod(term);
        }

        return term;
    }

    protected Term transformProgramMethod(Term term) {

        return term;
    }

    protected Term transformJunctor(Term term) throws TermTransformerException {

        if (isAnd(term)) {
            return transformAnd(term);

        } else if (isOr(term)) {
            return transformOr(term);

        } else if (isEquals(term)) {
            return transformEquals(term);

        } else if (isNot(term)) {
            return transformNot(term);
        }

        throw new TermTransformerException("Unsupported Junctor: "
                + term.op().name());
    }

    protected Term transformNot(Term term) throws TermTransformerException {

        Term newChild = transformTerm(term.sub(0));

        return termFactory.createTerm(Junctor.NOT, newChild);
    }

    protected Term transformAnd(Term term) throws TermTransformerException {

        Term firstChild = transformTerm(term.sub(0));
        Term secondChild = transformTerm(term.sub(1));

        return termFactory.createTerm(Junctor.AND, firstChild, secondChild);
    }

    protected Term transformOr(Term term) throws TermTransformerException {

        Term firstChild = transformTerm(term.sub(0));
        Term secondChild = transformTerm(term.sub(1));

        return termFactory.createTerm(Junctor.OR, firstChild, secondChild);
    }

    protected Term transformEquals(Term term) throws TermTransformerException {

        Term firstChild = transformTerm(term.sub(0));
        Term secondChild = transformTerm(term.sub(1));

        return termFactory.createTerm(term.op(), firstChild, secondChild);
    }
}
