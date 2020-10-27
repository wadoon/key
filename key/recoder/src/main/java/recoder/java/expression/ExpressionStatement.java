package recoder.java.expression;

import recoder.java.Expression;
import recoder.java.LoopInitializer;

public interface ExpressionStatement extends Expression, LoopInitializer {
    ExpressionStatement deepClone();
}
