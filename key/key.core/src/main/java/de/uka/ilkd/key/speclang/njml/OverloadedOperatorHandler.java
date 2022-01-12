package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.translation.JavaIntegerSemanticsHelper;
import de.uka.ilkd.key.speclang.translation.SLExceptionFactory;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;

import javax.annotation.Nullable;
import java.util.ArrayList;
import java.util.List;

/**
 * This class handles the operator during the JML translation {@link Translator}.
 *
 * @author Alexander Weigl
 * @version 1 (1/9/22)
 */
public class OverloadedOperatorHandler {
    /**
     * Enumeration of known operators, that are overloaded for JML types.
     */
    public enum JmlOperator {
        ADDITION, SUBTRACT, MULTIPLICATION, DIVISION, MODULO,
        BIT_AND, BIT_OR, BIT_XOR, BIT_NEGATE,
        SHIFT_RIGHT, SHIFT_LEFT, UNSIGNED_SHIFT_RIGHT,
        LESS_THAN, GREATER_THAN, GREATER_THAN_EQUALS, LESS_THAN_EQUALS;
    }

    /**
     * Implement this interface and register it to
     * {@link OverloadedOperatorHandler#OverloadedOperatorHandler(Services, SLExceptionFactory)}
     * to add new overloading to the operators.
     */
    public interface Handler {
        /**
         * Handling the construction of the binary, if this handler is applicable.
         * Return null, if this handler is not applicable for the given types.
         *
         * @param op    the JML operator
         * @param left  left side of the binary expression
         * @param right right side of the binary expression
         * @return null if this handler is not suitable for the given expression/types.
         * @throws SLTranslationException if this handler supports the given expression,
         *                                but something failed during the construction
         */
        @Nullable
        SLExpression build(JmlOperator op, SLExpression left, SLExpression right) throws SLTranslationException;
    }

    private final List<Handler> handlers = new ArrayList<>();

    public OverloadedOperatorHandler(Services services, SLExceptionFactory exc) {
        handlers.add(new BinaryBooleanHandler(services));
        handlers.add(new SequenceHandler(services));
        handlers.add(new LocSetHandler(services));
        handlers.add(new JavaIntegerSemanticsHelper(services, exc));
    }

    @Nullable
    public SLExpression build(JmlOperator op, SLExpression left, SLExpression right) throws SLTranslationException {
        for (Handler handler : handlers) {
            var term = handler.build(op, left, right);
            if (term != null) {
                return term;
            }
        }
        return null;
    }


    public static class SequenceHandler implements Handler {
        private final SeqLDT ldtSequence;
        private final TermBuilder tb;

        public SequenceHandler(Services services) {
            ldtSequence = services.getTypeConverter().getSeqLDT();
            tb = services.getTermBuilder();
        }

        @Nullable
        @Override
        public SLExpression build(JmlOperator op, SLExpression left, SLExpression right) throws SLTranslationException {
            if (left.getTerm().sort() == ldtSequence.targetSort() &&
                    right.getTerm().sort() == ldtSequence.targetSort()) {
                if (op == JmlOperator.ADDITION) {
                    return new SLExpression(tb.seqConcat(left.getTerm(), right.getTerm()));
                }
            }
            return null;
        }
    }

    public static class LocSetHandler implements Handler {
        private final LocSetLDT ldt;
        private final TermBuilder tb;

        public LocSetHandler(Services services) {
            ldt = services.getTypeConverter().getLocSetLDT();
            tb = services.getTermBuilder();
        }

        @Nullable
        @Override
        public SLExpression build(JmlOperator op, SLExpression left, SLExpression right) throws SLTranslationException {
            final var l = left.getTerm();
            final var r = right.getTerm();
            if (l.sort() == ldt.targetSort() && r.sort() == ldt.targetSort()) {
                switch (op) {
                    case ADDITION:
                    case BIT_OR:
                        return new SLExpression(tb.union(l, r));
                    case SUBTRACT:
                        return new SLExpression(tb.setMinus(l, r));
                    case BIT_AND:
                        return new SLExpression(tb.intersect(l, r));
                    case LESS_THAN:
                        return new SLExpression(tb.subset(l, r));
                    case LESS_THAN_EQUALS:
                        return new SLExpression(tb.and(tb.subset(l, r), tb.equals(l, r)));
                    case GREATER_THAN:
                        return new SLExpression(tb.subset(r, l));
                    case GREATER_THAN_EQUALS:
                        return new SLExpression(tb.and(tb.subset(r, l), tb.equals(l, r)));
                }
            }
            return null;
        }
    }

    private static class BinaryBooleanHandler implements Handler {
        private final Sort sortBoolean;
        private final TermBuilder tb;

        public BinaryBooleanHandler(Services services) {
            sortBoolean = services.getTypeConverter().getBooleanLDT().targetSort();
            tb = services.getTermBuilder();
        }

        @Nullable
        @Override
        public SLExpression build(JmlOperator op, SLExpression left, SLExpression right) throws SLTranslationException {
            if ((left.getTerm().sort() == sortBoolean || left.getTerm().sort() == Sort.FORMULA)
                    && (right.getTerm().sort() == sortBoolean || right.getTerm().sort() == Sort.FORMULA)) {
                final var t1 = tb.convertToFormula(left.getTerm());
                final var t2 = tb.convertToFormula(right.getTerm());
                switch (op) {
                    case BIT_AND:
                        return new SLExpression(tb.and(t1, t2));
                    case BIT_OR:
                        return new SLExpression(tb.or(t1, t2));
                    case BIT_XOR:
                        return new SLExpression(tb.or(tb.and(t1, tb.not(t2)), tb.and(tb.not(t1), t2)));
                }
            }
            return null;
        }
    }
}
