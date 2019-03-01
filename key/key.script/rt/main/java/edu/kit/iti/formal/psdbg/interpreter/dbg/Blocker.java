package edu.kit.iti.formal.psdbg.interpreter.dbg;

import edu.kit.iti.formal.psdbg.interpreter.Evaluator;
import edu.kit.iti.formal.psdbg.interpreter.Interpreter;
import edu.kit.iti.formal.psdbg.interpreter.exceptions.InterpreterRuntimeException;
import edu.kit.iti.formal.psdbg.parser.ast.ASTNode;
import edu.kit.iti.formal.psdbg.parser.types.SimpleType;
import lombok.Getter;
import lombok.RequiredArgsConstructor;
import lombok.val;

import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Predicate;
import java.util.function.Supplier;

public abstract class Blocker {
    public interface BlockPredicate extends Predicate<ASTNode> {
    }


    @RequiredArgsConstructor
    public static class BreakpointLine<T> implements BlockPredicate {
        @Getter
        private final Interpreter<T> interpreter;

        @Getter
        private final Set<Breakpoint> breakpoints = new HashSet<>();

        private final Breakpoint cmp = new Breakpoint(null, 0);

        @Override
        public boolean test(ASTNode node) {
            for (Breakpoint brkpt : getBreakpoints()) {
                // check file name
                if (brkpt.getSourceName().equals(node.getOrigin())) {
                    // check line
                    if (brkpt.getLineNumber() == node.getStartPosition().getLineNumber()) {
                        // if there is no condition
                        if (brkpt.getConditionAst() == null) {
                            return true; // no condition ==> trigger
                        } else { // if there is a condition, we check:
                            Evaluator<T> evaluator = new Evaluator<>(interpreter.getSelectedNode().getAssignments(), interpreter.getSelectedNode());
                            val v = evaluator.eval(brkpt.getConditionAst());
                            if (v.getType() != SimpleType.BOOL)
                                throw new InterpreterRuntimeException(
                                        String.format("Condition %s of breakpoint %s returned type %s",
                                                brkpt.getCondition(), brkpt, v.getType()));
                            if (v.getData() == Boolean.TRUE)
                                return true;
                        }
                    }
                }
            }
            return false;
        }
    }

    public static class CounterBlocker implements BlockPredicate {
        @Getter
        private final AtomicInteger stepUntilBlock = new AtomicInteger(-1);

        public CounterBlocker(int steps) {
            stepUntilBlock.set(steps);
        }

        @Override
        public boolean test(ASTNode astNode) {
            int value;
            if ((value = stepUntilBlock.decrementAndGet()) >= 0) {
                return 0 == value;
            }
            return false;
        }

        public void deactivate() {
            stepUntilBlock.set(-1);
        }
    }

    @RequiredArgsConstructor
    public static class UntilNode implements BlockPredicate {
        @Getter
        private final ASTNode node;

        @Override
        public boolean test(ASTNode astNode) {
            return node.equals(astNode);
        }
    }

    @RequiredArgsConstructor
    public static class NextWithParent implements BlockPredicate {
        @Getter
        private final ASTNode parent;

        @Override
        public boolean test(ASTNode astNode) {
            return parent.equals(astNode.getParent());
        }
    }

    @RequiredArgsConstructor
    public static class SmallerContext implements BlockPredicate {
        private final int depth;

        private final Supplier<Integer> currenDepth;

        @Override
        public boolean test(ASTNode astNode) {
            return currenDepth.get() <= depth;
        }
    }


    @RequiredArgsConstructor
    public static class ParentInContext implements BlockPredicate {
        @Getter
        private final ASTNode[] context;

        @Override
        public boolean test(ASTNode astNode) {
            for (ASTNode node : context) {
                if (astNode.isAncestor(node))
                    return true;
            }
            return false;
        }
    }


}
