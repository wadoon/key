package recoder.java;

public interface ScopeDefiningElement extends NonTerminalProgramElement {
    boolean isDefinedScope();

    void setDefinedScope(boolean paramBoolean);
}
