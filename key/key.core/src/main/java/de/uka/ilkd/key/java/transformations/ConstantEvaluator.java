package de.uka.ilkd.key.java.transformations;

import com.github.javaparser.ast.expr.Expression;
import jdk.jshell.JShell;
import jdk.jshell.SnippetEvent;

import java.util.List;
import java.util.Optional;

/**
 * @author Alexander Weigl
 * @version 1 (11/2/21)
 */
public class ConstantEvaluator {
    static JShell js = JShell.create();

    public boolean isCompileTimeConstant(Expression expr) throws EvaluationException {
        List<SnippetEvent> value = js.eval(expr.toString());
        assert value.size() == 1;
        SnippetEvent evt = value.get(0);
        if(evt.exception()!=null){
            throw new EvaluationException("Could not evaluate " + expr, evt.exception());
        }

        String result = evt.value();
        return true;
        /*if(Character.isDigit(result.charAt(0))){

        }*/
    }
}
