package edu.kit.iti.formal.psdbg.parser.function;

import edu.kit.iti.formal.psdbg.parser.NotWelldefinedException;
import edu.kit.iti.formal.psdbg.parser.Visitor;
import edu.kit.iti.formal.psdbg.parser.ast.FunctionCall;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import edu.kit.iti.formal.psdbg.parser.types.Type;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (10.11.17)
 */
public interface ScriptFunction {
    String getName();

    Type getType(List<Type> types)
            throws NotWelldefinedException;

    Value eval(Visitor<Value> val, FunctionCall call);
}
