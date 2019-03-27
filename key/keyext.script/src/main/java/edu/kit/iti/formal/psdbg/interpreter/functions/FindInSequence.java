package edu.kit.iti.formal.psdbg.interpreter.functions;

import edu.kit.iti.formal.psdbg.interpreter.Evaluator;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.interpreter.matcher.KeYMatcher;
import edu.kit.iti.formal.psdbg.parser.NotWelldefinedException;
import edu.kit.iti.formal.psdbg.parser.Visitor;
import edu.kit.iti.formal.psdbg.parser.ast.FunctionCall;
import edu.kit.iti.formal.psdbg.parser.ast.MatchExpression;
import edu.kit.iti.formal.psdbg.parser.ast.Variable;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import edu.kit.iti.formal.psdbg.parser.function.ScriptFunction;
import edu.kit.iti.formal.psdbg.parser.types.SimpleType;
import edu.kit.iti.formal.psdbg.parser.types.TermType;
import edu.kit.iti.formal.psdbg.parser.types.Type;
import edu.kit.iti.formal.psdbg.parser.types.TypeFacade;

import java.util.Collections;
import java.util.List;

/**
 * <h3>Examples</h3>
 * <code><pre>
 *     * find(match `f(?X)`) => f(x)
 *     * find(match ``) =>
 * </pre></code>
 *
 * @author Alexander Weigl
 * @version 1 (10.11.17)
 */
public class FindInSequence implements ScriptFunction {
    public static final List<Type> TYPES =
            Collections.singletonList(SimpleType.PATTERN);

    @Override
    public String getName() {
        return "find";
    }

    @Override
    public Type getType(List<Type> types) throws NotWelldefinedException {
        if (!TYPES.equals(types))
            throw new NotWelldefinedException("Wrong type of parameter for " + getName(), null);
        return new TermType();
    }

    @Override
    public Value eval(Visitor<Value> val, FunctionCall call)
            throws IllegalArgumentException {
        Evaluator<KeyData> e = (Evaluator<KeyData>) val;
        try {
            MatchExpression match = (MatchExpression) call.getArguments().get(0);
            //Signature sig = match.getSignature();
            Value pattern = e.eval(match.getPattern());
            KeYMatcher matcher = (KeYMatcher) e.getMatcher();
            if (TypeFacade.isTerm(pattern.getType())) {
                List<VariableAssignment> va = matcher.matchSeq(e.getGoal(), (String) pattern.getData());
                if (va.isEmpty()) {
                    throw new IllegalArgumentException("No match found for " + match.getPattern());
                } else {
                    Value rt = va.get(0).getValue(new Variable("rt"));
                    if (rt == null)
                        throw new IllegalStateException("Binding 'rt' not defined in pattern: " + match.getPattern());
                    return rt;
                }
            } else {
                throw new IllegalArgumentException("Matching only possible on terms.");
            }

        } catch (ClassCastException exc) {
            throw new IllegalStateException("Excepted a match expression as first argument found: " + call.getArguments().get(0),
                    exc);
        }
    }

}
