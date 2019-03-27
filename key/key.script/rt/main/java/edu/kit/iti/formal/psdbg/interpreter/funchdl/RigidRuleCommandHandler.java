package edu.kit.iti.formal.psdbg.interpreter.funchdl;

import edu.kit.iti.formal.psdbg.interpreter.Interpreter;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.parser.ast.CallStatement;

public class RigidRuleCommandHandler implements CommandHandler<KeyData> {
    @Override
    public boolean handles(CallStatement call, KeyData data) throws IllegalArgumentException {
        return true;
    }

    @Override
    public void evaluate(Interpreter<KeyData> interpreter, CallStatement call, VariableAssignment params, KeyData data) {

//        Evaluator evaluator = new Evaluator(g.getAssignments(), g);
//        evaluator.setMatcher(interpreter.getMatcherApi());
//taclet.getExecutor().apply(env.getLoadedProof().root(), env.getServices());
    }
}
