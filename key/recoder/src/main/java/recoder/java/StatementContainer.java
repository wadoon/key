package recoder.java;

public interface StatementContainer extends NonTerminalProgramElement {
    int getStatementCount();

    Statement getStatementAt(int paramInt);
}
