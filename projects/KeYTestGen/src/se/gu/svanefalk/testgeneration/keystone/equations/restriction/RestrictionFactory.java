package se.gu.svanefalk.testgeneration.keystone.equations.restriction;

import java.util.HashMap;
import java.util.Map;

import org.apache.commons.math3.fraction.Fraction;

public class RestrictionFactory {

    private static RestrictionFactory instance = null;

    public static RestrictionFactory getInstance() {

        if (RestrictionFactory.instance == null) {
            RestrictionFactory.instance = new RestrictionFactory();
        }
        return RestrictionFactory.instance;
    }

    public IRestriction createRangeRestriction(final Fraction lowerLimit,
            final Fraction upperLimit) {

        assert upperLimit != null;
        assert lowerLimit != null;

        return new IntervalRestriction(lowerLimit, upperLimit);
    }

    public IRestriction createGreaterOrEqualsRestriction(final Fraction value) {

        assert value != null;

        return new GreaterOrEqualsRestriction(value);
    }

    public IRestriction createLessOrEqualsRestriction(final Fraction value) {

        assert value != null;

        return new LessOrEqualsRestriction(value);
    }

    private class GreaterOrEqualsRestriction extends FractionRestrictions {

        public GreaterOrEqualsRestriction(Fraction bound) {
            this.bound = bound;
        }

        private final Fraction bound;

        @Override
        public Fraction makeConform(Fraction value) {

            if (greaterOrEquals(value, bound)) {
                return value;
            } else {
                return new Fraction(bound.getNumerator(),
                        bound.getDenominator());
            }
        }
    }

    private class LessOrEqualsRestriction extends FractionRestrictions {

        private final Fraction bound;

        public LessOrEqualsRestriction(Fraction bound) {
            super();
            this.bound = bound;
        }

        @Override
        public Fraction makeConform(Fraction value) {

            if (lessOrEquals(value, bound)) {
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

        public IntervalRestriction(Fraction lowerBound, Fraction upperBound) {
            this.enforceLowerBound = RestrictionFactory.getInstance().createLessOrEqualsRestriction(
                    lowerBound);
            this.enforceUpperBound = RestrictionFactory.getInstance().createLessOrEqualsRestriction(
                    upperBound);
        }

        @Override
        public Fraction makeConform(Fraction value) {
            return enforceLowerBound.makeConform(enforceUpperBound.makeConform(value));
        }
    }

    private abstract class FractionRestrictions implements IRestriction {

        protected final boolean greaterOrEquals(Fraction left, Fraction right) {
            return left.getNumerator() * right.getDenominator() >= left.getDenominator()
                    * right.getNumerator();
        }

        protected final boolean lessOrEquals(Fraction left, Fraction right) {
            return left.getNumerator() * right.getDenominator() <= left.getDenominator()
                    * right.getNumerator();
        }
    }
}