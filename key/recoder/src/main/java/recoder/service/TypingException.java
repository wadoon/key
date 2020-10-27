package recoder.service;

import recoder.ModelException;
import recoder.java.Expression;

public class TypingException extends ModelException {
    private static final long serialVersionUID = -1396794920221995373L;

    private final Expression expression;

    public TypingException(Expression expr) {
        this.expression = expr;
    }

    public TypingException(String s, Expression expr) {
        super(s);
        this.expression = expr;
    }

    public Expression getUntypableExpression() {
        return this.expression;
    }
}
