// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import java.util.HashMap;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * This method performs type checking and sort inference by supplying methods
 * previously defined by the {@link Operator} class which, however, were not
 * Operator-relatex.
 *
 * @author Dominic Scheurer
 */
public abstract class TypeCheckingAndInferenceService<O extends Operator> {

    private static final HashMap<Class<?>, TypeCheckingAndInferenceService<?>> CHECKERS =
            new HashMap<Class<?>, TypeCheckingAndInferenceService<?>>();

    static {
        CHECKERS.put(AbstractSortedOperator.class,
                new AbstractSortedOperatorTypeCheckingAndInferenceService());
        CHECKERS.put(IfExThenElse.class,
                new IfExThenElseTypeCheckingAndInferenceService());
        CHECKERS.put(IfThenElse.class,
                new IfThenElseTypeCheckingAndInferenceService());
        CHECKERS.put(SubstOp.class,
                new SubstOpTypeCheckingAndInferenceService());
        CHECKERS.put(UpdateApplication.class,
                new UpdateApplicationTypeCheckingAndInferenceService());
    }

    // /////////////////////////////////// //
    // ///////// GENERIC FACTORY ///////// //
    // /////////////////////////////////// //

    @SuppressWarnings("unchecked")
    private static <C extends Operator> TypeCheckingAndInferenceService<C> getTypeCheckerFor(
            Class<C> clazz) {
        if (CHECKERS.containsKey(clazz)) {
            return (TypeCheckingAndInferenceService<C>) CHECKERS.get(clazz);
        }
        else {
            throw new UnsupportedOperationException(
                    "There is no type checker and sort inference service registred for class "
                            + clazz.getName());
        }
    }

    @SuppressWarnings("unchecked")
    public static <C extends Operator> TypeCheckingAndInferenceService<C> getTypeCheckerFor(
            C op) {
        TypeCheckingAndInferenceService<C> result =
                (TypeCheckingAndInferenceService<C>) CHECKERS
                        .get(op.getClass());

        for (Class<?> c : CHECKERS.keySet()) {
            if (c.isInstance(op)) {
                result = (TypeCheckingAndInferenceService<C>) CHECKERS.get(c);
                CHECKERS.put(op.getClass(), result);
                return result;
            }
        }

        throw new UnsupportedOperationException(
                "There is no type checker and sort inference service registred for class "
                        + op.getClass().getName());
    }

    // /////////////////////////////////// //
    // /////// POLYMORPHIC GETTERS /////// //
    // /////////////////////////////////// //

    public static TypeCheckingAndInferenceService<AbstractSortedOperator> getChecker(
            AbstractSortedOperator op) {
        return getTypeCheckerFor(AbstractSortedOperator.class);
    }

    public static TypeCheckingAndInferenceService<IfExThenElse> getChecker(
            IfExThenElse op) {
        return getTypeCheckerFor(IfExThenElse.class);
    }

    public static TypeCheckingAndInferenceService<IfThenElse> getChecker(
            IfThenElse op) {
        return getTypeCheckerFor(IfThenElse.class);
    }

    public static TypeCheckingAndInferenceService<SubstOp> getChecker(SubstOp op) {
        return getTypeCheckerFor(SubstOp.class);
    }

    public static TypeCheckingAndInferenceService<UpdateApplication> getChecker(
            UpdateApplication op) {
        return getTypeCheckerFor(UpdateApplication.class);
    }

    // /////////////////////////////////// //
    // //////// PUBLIC__INTERFACE //////// //
    // /////////////////////////////////// //

    public abstract Sort sort(ImmutableArray<Term> terms, O op);

    public abstract boolean additionalValidTopLevel(Term term, O op);

    /**
     * Checks whether the top level structure of the given @link Term is
     * syntactically valid, given the assumption that the top level operator of
     * the term is the same as this Operator. The assumption that the top level
     * operator and the term are equal is NOT checked.
     * 
     * @return true iff the top level structure of the {@link Term} is valid.
     */
    public abstract boolean validTopLevel(Term term, O op);

    // /////////////////////////////////// //
    // ///////// TEMPLATE__CLASS ///////// //
    // /////////////////////////////////// //

    static abstract class DefaultTypeCheckingAndInferenceService<O extends Operator>
            extends TypeCheckingAndInferenceService<O> {
        @Override
        public boolean validTopLevel(Term term, O op) {
            if (op.arity() != term.arity() || op.arity() != term.subs().size()
                    || op.bindsVars() != term.boundVars().isEmpty()) {
                return false;
            }

            for (int i = 0, n = op.arity(); i < n; i++) {
                if (term.sub(i) == null) {
                    return false;
                }
            }

            return additionalValidTopLevel(term, op);
        }
    }

    // /////////////////////////////////// //
    // //////// CONCRETE CHECKERS //////// //
    // /////////////////////////////////// //

    static class AbstractSortedOperatorTypeCheckingAndInferenceService extends
            DefaultTypeCheckingAndInferenceService<AbstractSortedOperator> {

        private AbstractSortedOperatorTypeCheckingAndInferenceService() {
            // This class should be a Singleton.
        }

        public Sort sort(ImmutableArray<Term> terms, AbstractSortedOperator op) {
            return op.sort();
        }

        public boolean additionalValidTopLevel(Term term,
                AbstractSortedOperator op) {
            for (int i = 0, n = op.arity(); i < n; i++) {
                if (!possibleSub(i, term.sub(i), op)) {
                    return false;
                }
            }
            return true;
        }

        /**
         * checks if a given Term could be subterm (at the at'th subterm
         * position) of a term with this function at its top level. The validity
         * of the given subterm is NOT checked.
         * 
         * @param at
         *            theposition of the term where this method should check the
         *            validity.
         * @param possibleSub
         *            the subterm to be ckecked.
         * @return true iff the given term can be subterm at the indicated
         *         position
         */
        private boolean possibleSub(int at, Term possibleSub,
                AbstractSortedOperator op) {
            final Sort s = possibleSub.sort();

            return s == AbstractTermTransformer.METASORT
                    || s instanceof ProgramSVSort
                    || op.argSort(at) == AbstractTermTransformer.METASORT
                    || op.argSort(at) instanceof ProgramSVSort
                    || s.extendsTrans(op.argSort(at));
        }
    }

    static class IfExThenElseTypeCheckingAndInferenceService extends
            DefaultTypeCheckingAndInferenceService<IfExThenElse> {

        private IfExThenElseTypeCheckingAndInferenceService() {
            // This class should be a Singleton.
        }

        public Sort sort(ImmutableArray<Term> terms, IfExThenElse op) {
            return terms.get(1).sort();
        }

        public boolean additionalValidTopLevel(Term term, IfExThenElse op) {
            for (QuantifiableVariable var : term.varsBoundHere(0)) {
                if (!var.sort().name().toString().equals("int")) {
                    return false;
                }
            }

            final Sort s0 = term.sub(0).sort();
            final Sort s1 = term.sub(1).sort();
            final Sort s2 = term.sub(2).sort();

            return s0 == Sort.FORMULA && s1.equals(s2);
        }
    }

    static class IfThenElseTypeCheckingAndInferenceService extends
            DefaultTypeCheckingAndInferenceService<IfThenElse> {

        private IfThenElseTypeCheckingAndInferenceService() {
            // This class should be a Singleton.
        }

        public Sort sort(ImmutableArray<Term> terms, IfThenElse op) {
            final Sort s2 = terms.get(1).sort();
            final Sort s3 = terms.get(2).sort();
            if (s2 instanceof ProgramSVSort
                    || s2 == AbstractTermTransformer.METASORT) {
                return s3;
            }
            else if (s3 instanceof ProgramSVSort
                    || s3 == AbstractTermTransformer.METASORT) {
                return s2;
            }
            else {
                return getCommonSuperSort(s2, s3);
            }
        }

        public boolean additionalValidTopLevel(Term term, IfThenElse op) {
            final Sort s0 = term.sub(0).sort();
            final Sort s1 = term.sub(1).sort();
            final Sort s2 = term.sub(2).sort();

            return s0 == Sort.FORMULA
                    && (s1 == Sort.FORMULA) == (s2 == Sort.FORMULA)
                    && s1 != Sort.UPDATE && s2 != Sort.UPDATE;
        }

        private Sort getCommonSuperSort(Sort s1, Sort s2) {
            if (s1 == Sort.FORMULA) {
                assert s2 == Sort.FORMULA : "Sorts FORMULA and " + s2
                        + " are incompatible.";
                return Sort.FORMULA;
            }
            else if (s1.extendsTrans(s2)) {
                return s2;
            }
            else if (s2.extendsTrans(s1)) {
                return s1;
            }
            else if (s1 instanceof NullSort || s2 instanceof NullSort) {
                return Sort.ANY;
            }
            else {
                Sort result = Sort.ANY;
                final ImmutableSet<Sort> set1 = s1.extendsSorts();
                final ImmutableSet<Sort> set2 = s2.extendsSorts();
                assert set1 != null : "null for sort: " + s1;
                assert set2 != null : "null for sort: " + s2;

                for (final Sort sort1 : set1) {
                    if (set2.contains(sort1)) {
                        if (result == Sort.ANY) {
                            result = sort1;
                        }
                        else {
                            // not uniquely determinable
                            return Sort.ANY;
                        }
                    }
                }

                return result;
            }
        }
    }

    static class SubstOpTypeCheckingAndInferenceService extends
            DefaultTypeCheckingAndInferenceService<SubstOp> {

        private SubstOpTypeCheckingAndInferenceService() {
            // This class should be a Singleton.
        }

        public Sort sort(ImmutableArray<Term> terms, SubstOp op) {
            if (terms.size() == 2) {
                return terms.get(1).sort();
            }
            else {
                throw new IllegalArgumentException("Cannot determine sort of "
                        + "invalid term (Wrong arity).");
            }
        }

        public boolean additionalValidTopLevel(Term term, SubstOp op) {
            if (term.varsBoundHere(1).size() != 1) {
                return false;
            }
            Sort substSort = term.sub(0).sort();
            Sort varSort = term.varsBoundHere(1).get(0).sort();
            return substSort.extendsTrans(varSort);
        }
    }

    static class UpdateApplicationTypeCheckingAndInferenceService extends
            DefaultTypeCheckingAndInferenceService<UpdateApplication> {

        private UpdateApplicationTypeCheckingAndInferenceService() {
            // This class should be a Singleton.
        }

        public Sort sort(ImmutableArray<Term> terms, UpdateApplication op) {
            return terms.get(1).sort();
        }

        public boolean additionalValidTopLevel(Term term, UpdateApplication op) {
            return term.sub(0).sort() == Sort.UPDATE;
        }
    }
}
