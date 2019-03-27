package edu.kit.iti.formal.psdbg.parser.ast;

import edu.kit.iti.formal.psdbg.parser.NotWelldefinedException;
import edu.kit.iti.formal.psdbg.parser.ScriptLanguageParser;
import edu.kit.iti.formal.psdbg.parser.Visitor;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import edu.kit.iti.formal.psdbg.parser.function.ScriptFunction;
import edu.kit.iti.formal.psdbg.parser.types.Type;
import lombok.Getter;
import lombok.NoArgsConstructor;
import lombok.Setter;
import lombok.ToString;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (10.11.17)
 */
@Getter
@Setter
@ToString
@NoArgsConstructor
public class FunctionCall extends Expression<ScriptLanguageParser.FunctionContext> {
    private ScriptFunction function;
    private List<Expression> arguments = new ArrayList<>(10);

    public FunctionCall(ScriptFunction func, List<Expression> arguments) {
        this.function = func;
        arguments.forEach(a -> this.arguments.add(a.copy()));
    }

    @Override
    public boolean hasMatchExpression() {
        return arguments.stream().anyMatch(Expression::hasMatchExpression);
    }

    @Override
    public int getPrecedence() {
        return 0;
    }

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public Expression copy() {
        return new FunctionCall(function, arguments);
    }

    @Override
    public Type getType(Signature signature)
            throws NotWelldefinedException {
        List<Type> argtypes = new ArrayList<>();
        for (Expression e : arguments) {
            argtypes.add(e.getType(signature));
        }
        return function.getType(argtypes);
    }
}
