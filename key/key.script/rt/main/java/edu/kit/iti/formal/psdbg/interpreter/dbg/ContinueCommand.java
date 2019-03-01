package edu.kit.iti.formal.psdbg.interpreter.dbg;

import edu.kit.iti.formal.psdbg.parser.ast.ASTNode;

import java.util.Arrays;
import java.util.function.Supplier;

/**
 * Continue Command if interpreter stopped at a breakpoint
 *
 * @param <T>
 */
public class ContinueCommand<T> extends DebuggerCommand<T> {
    @Override
    public void execute(DebuggerFramework<T> dbg) {
        PTreeNode<T> statePointer = dbg.getStatePointer();
        if (statePointer != null) {
            PTreeNode<T> stepOverPointer = statePointer.getStepOver();
            if (stepOverPointer != null) {
                dbg.setStatePointer(stepOverPointer);
                return;
            }

            ASTNode[] ctx = statePointer.getContext();
            //statePointer stands on the main script, we add the script itself to the context
            if (statePointer.getContext().length == 0) {
                ctx = Arrays.copyOf(ctx, ctx.length + 1);
                ctx[ctx.length - 1] = statePointer.getStatement();
            }

            Supplier<Integer> currenDepth = () -> dbg.getStatePointer().getContext().length;
            dbg.release();
        } else {

        }
    }
}

