package recoder.java;

public interface Statement extends ProgramElement {
    StatementContainer getStatementContainer();

    void setStatementContainer(StatementContainer paramStatementContainer);

    Statement deepClone();
}
