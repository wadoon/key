package se.gu.svanefalk.testgeneration.keystone.equations.restriction;

import org.apache.commons.math3.fraction.Fraction;

public class RestrictionFactory {

    private abstract class FractionRestrictions implements IRestriction {

        protected final boolean greaterOrEquals(final Fraction left,
                final Fraction right) {
            return (left.getNumerator() * right.getDenominator()) >= (left.getDenominator() * right.getNumerator());
        }

        protected final boolean lessOrEquals(final Fraction left,
                final Fraction right) {
            return (left.getNumerator() * right.getDenominator()) <= (left.getDenominator() * right.getNumerator());
        }
    }

    private class GreaterOrEqualsRestriction extends FractionRestrictions {

        private final Fraction bound;

        public GreaterOrEqualsRestriction(final Fraction bound) {
            this.bound = bound;
        }

        @Override
        public Fraction makeConform(final Fraction value) {

            if (greaterOrEquals(value, bound)) {
                return value;
            } else {
                return new Fraction(bound.getNumerator(),
                        bound.getDenominator());
            }
        }
    }

    private class IntervalRestriction extends FractionRestrictions {

        private final IRestriction enforceLowerBound;
        private final IRestriction enforceUpperBound;

        public IntervalRestriction(final Fraction lowerBound,
                final Fraction upperBound) {
            enforceLowerBound = RestrictionFactory.getInstance().createLessOrEqualsRestriction(
                    lowerBound);
            enforceUpperBound = RestrictionFactory.getInstance().createLessOrEqualsRestriction(
                    upperBound);
        }

        @Override
        public Fraction makeConform(final Fraction value) {
            return enforceLowerBound.makeConform(enforceUpperBound.makeConform(value));
        }
    }

    private class LessOrEqualsRestriction extends FractionRestrictions {

        private final Fraction bound;

        public LessOrEqualsRestriction(final Fraction bound) {
            super();
            this.bound = bound;
        }

        @Override
        public Fraction makeConform(final Fraction value) {

            if (lessOrEquals(value, bound)) {
                return value;
            } else {
                return new Fraction(bound.getNumerator(),
                        bound.getDenominator());
            }
        }
    }

    public static final IRestriction greaterThanZeroRestriction;

    private static RestrictionFactory instance = null;

    public static final IRestriction integerValueRestriction;

    private static final Fraction maxInteger;

    private static final Fraction minInteger;

    static {
        final RestrictionFactory restrictionFactory = RestrictionFactory.getInstance();

        maxInteger = new Fraction(Integer.MAX_VALUE);
        minInteger = new Fraction(Integer.MIN_VALUE);
        integerValueRestriction = restrictionFactory.createRangeRestriction(
                RestrictionFactory.minInteger, RestrictionFactory.maxInteger);
        greaterThanZeroRestriction = restrictionFactory.createGreaterOrEqualsRestriction(new Fraction(
                0));
    }

    public static RestrictionFactory getInstance() {

        if (RestrictionFactory.instance == null) {
            RestrictionFactory.instance = new RestrictionFactory();
        }
        return RestrictionFactory.instance;
    }

    public IRestriction createGreaterOrEqualsRestriction(final Fraction value) {

        assert value != null;

        return new GreaterOrEqualsRestriction(value);
    }

    public IRestriction createLessOrEqualsRestriction(final Fraction value) {

        assert value != null;

        return new LessOrEqualsRestriction(value);
    }

    public IRestriction createRangeRestriction(final Fraction lowerLimit,
            final Fraction upperLimit) {

        assert upperLimit != null;
        assert lowerLimit != null;

        return new IntervalRestriction(lowerLimit, upperLimit);
    }
}