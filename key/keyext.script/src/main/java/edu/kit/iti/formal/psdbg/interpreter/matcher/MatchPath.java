package edu.kit.iti.formal.psdbg.interpreter.matcher;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import lombok.Data;
import lombok.EqualsAndHashCode;

/**
 * @author Alexander Weigl
 * @version 1 (24.08.17)
 */
@Data
@EqualsAndHashCode(of = {"unit"})
public abstract class MatchPath<T, P> {
    public static final int SEQUENT_FORMULA_ROOT = -1;
    public static final int POSITION_ANTECEDENT = -2;
    public static final int POSITION_SUCCEDENT = -3;

    private final MatchPath<? extends P, ?> parent;
    private final T unit;
    private final int posInParent;

    private MatchPath(MatchPath<? extends P, ?> parent, T unit, int pos) {
        posInParent = pos;
        this.unit = unit;
        this.parent = parent;
    }

    public abstract PosInOccurrence pio();


    public Sequent getSequent() {
        if (getParent() != null)
            return getParent().getSequent();
        return null;
    }

    public SequentFormula getSequentFormula() {
        if (getParent() != null)
            return getParent().getSequentFormula();
        return null;
    }

    public abstract int depth();

    public String toString() {
        return unit.toString();
    }

    public static final class MPQuantifiableVariable extends MatchPath<QuantifiableVariable, Object> {

        public MPQuantifiableVariable(MatchPath<? extends Object, ?> parent, QuantifiableVariable unit, int pos) {
            super(parent, unit, pos);
        }

        @Override
        public PosInOccurrence pio() {
            return null;
        }

        @Override
        public Sequent getSequent() {
            return null;
        }

        @Override
        public SequentFormula getSequentFormula() {
            return null;
        }

        @Override
        public int depth() {
            return getParent().depth() + 1;
        }
    }

    public static class MPTerm extends MatchPath<Term, Object> {
        public MPTerm(MatchPath<? extends Object, ?> parent, Term unit, int pos) {
            super(parent, unit, pos);
        }

        @Override
        public PosInOccurrence pio() {
            if(getParent()==null) return null;
            PosInOccurrence pio = getParent().pio();
            if(getPosInParent()==SEQUENT_FORMULA_ROOT)
                return pio;
            return pio.down(getPosInParent());
        }

        @Override
        public int depth() {
            return getUnit().depth();
        }
    }

    public static class MPSequentFormula extends MatchPath<SequentFormula, Semisequent> {
        public MPSequentFormula(MatchPath<Semisequent, Sequent> parent, SequentFormula unit, int pos) {
            super(parent, unit, pos);
        }

        @Override
        public PosInOccurrence pio() {
            return new PosInOccurrence(getUnit(), PosInTerm.getTopLevel(),
                    getParent().getPosInParent() == POSITION_ANTECEDENT
            );
        }

        @Override
        public Sequent getSequent() {
            if (getParent() != null)
                return getParent().getSequent();
            return null;
        }

        @Override
        public SequentFormula getSequentFormula() {
            return getUnit();
        }

        @Override
        public int depth() {
            return getUnit().formula().depth();
        }
    }

    public static class MPSequent extends MatchPath<Sequent, Void> {
        public MPSequent(Sequent unit) {
            super(null, unit, SEQUENT_FORMULA_ROOT);
        }

        @Override
        public int depth() {
            return 0;
        }

        @Override
        public PosInOccurrence pio() {
            return null;
        }

        @Override
        public Sequent getSequent() {
            return getUnit();
        }

        @Override
        public SequentFormula getSequentFormula() {
            return null;
        }
    }

    public static class MPSemiSequent extends MatchPath<Semisequent, Sequent> {
        public MPSemiSequent(MPSequent parent, Semisequent unit, boolean antec) {
            super(parent, unit, antec ? POSITION_ANTECEDENT : POSITION_SUCCEDENT);
        }

        @Override
        public int depth() {
            return 1;
        }

        @Override
        public PosInOccurrence pio() {
            return null;
        }

        @Override
        public Sequent getSequent() {
            if (getParent() == null) return null;
            return getParent().getSequent();
        }

        @Override
        public SequentFormula getSequentFormula() {
            return null;
        }
    }
}
