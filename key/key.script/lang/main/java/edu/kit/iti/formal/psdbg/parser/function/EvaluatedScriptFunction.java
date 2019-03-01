package edu.kit.iti.formal.psdbg.parser.function;

import edu.kit.iti.formal.psdbg.parser.Visitor;
import edu.kit.iti.formal.psdbg.parser.ast.Expression;
import edu.kit.iti.formal.psdbg.parser.ast.FunctionCall;
import edu.kit.iti.formal.psdbg.parser.data.Value;

import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (10.11.17)
 */
public abstract class EvaluatedScriptFunction implements ScriptFunction {
    @Override
    public Value eval(Visitor<Value> val, FunctionCall call) {
        List<Value> values = call.getArguments().stream()
                .map(e -> (Value) e.accept(val))
                .collect(Collectors.toList());
        return eval(values, val);
    }

    protected abstract Value eval(List<Value> values,
                                  Visitor<Value> val);
}
