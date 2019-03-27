package edu.kit.iti.formal.psdbg.interpreter.funchdl;

import edu.kit.iti.formal.psdbg.interpreter.Interpreter;
import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.State;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.parser.ast.CallStatement;
import edu.kit.iti.formal.psdbg.parser.ast.Variable;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import lombok.Getter;
import lombok.RequiredArgsConstructor;

import java.math.BigInteger;

/**
 * @author Alexander Weigl
 * @version 1 (21.05.17)
 */
public abstract class BuiltinCommands {
    @RequiredArgsConstructor
    public abstract static class BuiltinCommand<T> implements CommandHandler<T> {
        @Getter
        private final String name;

        @Override
        public boolean handles(CallStatement call, T data) throws IllegalArgumentException {
            return name.equals(call.getCommand());
        }
    }

    public static class PrintCommand<T extends Object> extends BuiltinCommand<T> {
        public PrintCommand() {
            super("print_state");
        }

        @Override
        public void evaluate(Interpreter<T> interpreter, CallStatement call, VariableAssignment params, T data) {
            for (GoalNode<T> gn : interpreter.getCurrentGoals()) {
                System.out.format("%s %s%n  %s%n", gn == interpreter.getSelectedNode() ? "*" : " ", gn.getData(), gn.getAssignments().asMap());
            }
        }
    }

    public static class SplitCommand extends BuiltinCommand<String> {

        public SplitCommand() {
            super("split");
        }

        /**
         * Created by sarah on 5/17/17.
         */
        @Override
        public void evaluate(Interpreter<String> interpreter, CallStatement call, VariableAssignment params, String data) {
            Value<BigInteger> val = (Value<BigInteger>) params.getValues().getOrDefault(
                    new Variable("#2"),
                    Value.from(2));
            int num = val.getData().intValue();
            GoalNode<String> g = interpreter.getSelectedNode();
            State<String> s = interpreter.getCurrentState();
            State<String> state = new State<>(s.getGoals(), null);
            state.getGoals().remove(s.getSelectedGoalNode());
            for (char i = 0; i < num; i++) {
                state.getGoals().add(new GoalNode<>(g, g.getData() + "." + (char) ('a' + i), g.isClosed()));
            }
            interpreter.pushState(state);
        }
    }
}
