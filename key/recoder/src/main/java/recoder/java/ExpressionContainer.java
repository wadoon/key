package recoder.java;

public interface ExpressionContainer extends NonTerminalProgramElement {
    int getExpressionCount();

    Expression getExpressionAt(int paramInt);
}
