package edu.kit.iti.formal.psdbg.interpreter.exceptions;

import de.uka.ilkd.key.macros.scripts.RuleCommand;

import java.util.Map;

/**
 * Exception for not applicable rules
 *
 * @author grebing
 */
public class ScriptCommandNotApplicableException extends InterpreterRuntimeException {
    public ScriptCommandNotApplicableException(Exception e, RuleCommand c) {
        System.out.println("Call " + c.getName() + " was not applicable");
    }

    public ScriptCommandNotApplicableException(Exception e, RuleCommand c, Map<String, Object> params) {
        super(createMessage(c, params), e);
    }

    private static String createMessage(RuleCommand c, Map<String, Object> params) {
        StringBuilder sb = new StringBuilder();
        sb.append("Call " + c.getName() + " with parameters ");
        for (String s : params.keySet()) {
            sb.append(s).append(" ").append(params.get(s));
        }
        sb.append(" was not applicable");
        return sb.toString();
    }
}
