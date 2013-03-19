package de.uka.ilkd.key.testgeneration.util.parsers.transformers;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IfExThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.testgeneration.util.parsers.AbstractTermParser;
import de.uka.ilkd.key.testgeneration.util.parsers.TermParserException;

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
public abstract class AbstractTermTransformer extends AbstractTermParser
        implements ITermTransformer {

    /**
     * Used for constructing new {@link Term} instances.
     */
    protected final TermFactory termFactory = TermFactory.DEFAULT;

    /**
     * @return a {@link Term} representation of the boolean constant FALSE.
     */
    protected Term createFalseConstant() {
        final Name name = new Name("FALSE");
        final Sort sort = new SortImpl(new Name(AbstractTermParser.BOOLEAN));
        final Function function = new Function(name, sort);
        return this.termFactory.createTerm(function);
    }

    /**
     * @return a {@link Term} representation of the boolean constant TRUE.
     */
    protected Term createTrueConstant() {

        final Name name = new Name("TRUE");
        final Sort sort = new SortImpl(new Name(AbstractTermParser.BOOLEAN));
        final Function function = new Function(name, sort);
        return this.termFactory.createTerm(function);
    }

    /**
     * Transforms a {@link Term} representing the AND junctor.
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected Term transformAnd(final Term term)
            throws TermTransformerException {

        final Term firstChild = this.transformTerm(term.sub(0));
        final Term secondChild = this.transformTerm(term.sub(1));

        return this.termFactory
                .createTerm(Junctor.AND, firstChild, secondChild);
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
    protected Term transformBinaryFunction(final Term term)
            throws TermTransformerException {

        final Term firstChild = this.transformTerm(term.sub(0));
        final Term secondChild = this.transformTerm(term.sub(1));

        final Term newTerm = this.termFactory.createTerm(term.op(), firstChild,
                secondChild);

        return newTerm;
    }

    private Term transformBooleanConstant(final Term term) {
        return term;
    }

    /**
     * Transforms a {@link Term} representing {@link Equality}.
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected Term transformEquals(final Term term)
            throws TermTransformerException {

        final Term firstChild = this.transformTerm(term.sub(0));
        final Term secondChild = this.transformTerm(term.sub(1));

        return this.termFactory.createTerm(term.op(), firstChild, secondChild);
    }

    /**
     * Transforms a {@link Term} which represents some instance of a
     * {@link Function}.
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected Term transformFunction(final Term term)
            throws TermTransformerException {

        try {

            /*
             * Order is crucial for proper resolution here, as the precise,
             * legitimate parent-child relationships between various
             * Function-type terms are not excplicitly spelled out in terms of
             * type relationships.
             */
            if (this.isNullSort(term)) {
                return this.transformNull(term);
            }

            if (this.isSortDependingFunction(term)) {
                return this.transformSortDependentFunction(term);
            }

            if (this.isBinaryFunction(term)) {
                return this.transformBinaryFunction(term);
            }

            if (this.isUnaryFunction(term)) {
                return this.transformUnaryFunction(term);
            }

            if (this.isLiteral(term)) {
                return this.transformLiteral(term);
            }

            if (this.isObserverFunction(term)) {
                return this.transformObserverFunction(term);

            }

            if (this.isBooleanConstant(term)) {
                return this.transformBooleanConstant(term);
            }

        } catch (final TermParserException e) {

            throw new TermTransformerException(e.getMessage());
        }

        throw new TermTransformerException("Unsupported Function: "
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
    protected Term transformIfExThenElse(final Term term) {

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
    protected Term transformIfThenElse(final Term term) {

        return term;
    }

    /**
     * Transforms a {@link Term} representing a Junctor, i.e. AND, OR, NOT.
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected Term transformJunctor(final Term term)
            throws TermTransformerException {

        if (this.isAnd(term)) {
            return this.transformAnd(term);

        } else if (this.isOr(term)) {
            return this.transformOr(term);

        } else if (this.isEquals(term)) {
            return this.transformEquals(term);

        } else if (this.isNot(term)) {
            return this.transformNot(term);
        }

        throw new TermTransformerException("Unsupported Junctor: "
                + term.op().name());
    }

    /**
     * Transforms a {@link Term} representing a Literal.
     * 
     * @param term
     * @return
     * @throws TermTransformerException
     */
    protected Term transformLiteral(final Term term)
            throws TermTransformerException {

        /*
         * Literals may or may not declare children, such as 1(#);
         */
        if (!term.subs().isEmpty()) {
            final Term child = this.transformTerm(term.sub(0));
            return this.termFactory.createTerm(term.op(), child);
        } else {
            return term;
        }
    }

    /**
     * Transforms a {@link Term} which represents an {@link LocationVariable}
     * structure (i.e. its {@link Operator} is of this type).
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected Term transformLocationVariable(final Term term) {

        return term;
    }

    /**
     * Transforms a {@link Term} representing a the NOT junctor.
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected Term transformNot(final Term term)
            throws TermTransformerException {

        final Term newChild = this.transformTerm(term.sub(0));

        return this.termFactory.createTerm(Junctor.NOT, newChild);
    }

    /**
     * Transforms a {@link Term} which represents a null element, i.e. it has
     * the sort {@link NullSort}.
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected Term transformNull(final Term term) {

        return term;
    }

    /**
     * Transforms a {@link Term} representing an {@link ObserverFunction}.
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected Term transformObserverFunction(final Term term) {

        if (this.isProgramMethod(term)) {
            return this.transformProgramMethod(term);
        }

        return term;
    }

    /**
     * Transforms a {@link Term} representing an OR-junctor.
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected Term transformOr(final Term term) throws TermTransformerException {

        final Term firstChild = this.transformTerm(term.sub(0));
        final Term secondChild = this.transformTerm(term.sub(1));

        return this.termFactory.createTerm(Junctor.OR, firstChild, secondChild);
    }

    /**
     * Transforms a {@link Term} representing a {@link ProgramMethod}.
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected Term transformProgramMethod(final Term term) {

        return term;
    }

    /**
     * Transforms a {@link Term} which represents a {@link ProgramVariable}
     * structure (i.e. its {@link Operator} is of this type).
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    protected Term transformProgramVariable(final Term term)
            throws TermTransformerException {

        if (this.isLocationVariable(term)) {
            return this.transformLocationVariable(term);
        }

        throw new TermTransformerException("Unsupported SortedOperator: "
                + term.op().name());
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
    protected Term transformSortDependentFunction(final Term term) {

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
    protected Term transformSortedOperator(final Term term)
            throws TermTransformerException {

        if (this.isFunction(term)) {
            return this.transformFunction(term);
        }

        if (this.isEquals(term)) {
            return this.transformEquals(term);
        }

        if (this.isJunctor(term)) {
            return this.transformJunctor(term);
        }

        if (this.isProgramVariable(term)) {
            return this.transformProgramVariable(term);
        }

        throw new TermTransformerException("Unsupported SortedOperator: "
                + term.op().name());
    }

    /**
     * The top level function for transforming a {@link Term} instance. This
     * function will do a preliminary check to see whether the top-level
     * operator of the Term is a basic {@link Operator} or a
     * {@link SortedOperator}, and proceed with parsing from there.
     * 
     * @param term
     * @return
     */
    public Term transformTerm(final Term term) throws TermTransformerException {

        /*
         * Order matters here, since SortedOperator is a subclass of Operator.
         */
        if (this.isSortedOperator(term)) {
            return this.transformSortedOperator(term);

        } else if (this.isIfExThenElse(term)) {
            return this.transformIfExThenElse(term);

        } else if (this.isIfThenElse(term)) {
            return this.transformIfThenElse(term);

        }

        throw new TermTransformerException("Unsupported SortedOperator: "
                + term.op().name());
    }

    /**
     * Transforms a {@link Term} representing a unary function, such as NOT.
     * 
     * @param term
     *            the term
     * @return the transformed term
     */
    private Term transformUnaryFunction(final Term term)
            throws TermTransformerException {

        final Term child = this.transformTerm(term.sub(0));

        final Term newTerm = this.termFactory.createTerm(term.op(), child);

        return newTerm;
    }
}
