package recoder.java;

public interface Expression extends ProgramElement {
    ExpressionContainer getExpressionContainer();

    void setExpressionContainer(ExpressionContainer paramExpressionContainer);

    Expression deepClone();
}
