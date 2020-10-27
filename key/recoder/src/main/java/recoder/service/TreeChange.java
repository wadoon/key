package recoder.service;

import recoder.java.CompilationUnit;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;

public abstract class TreeChange {
    private final ProgramElement root;

    private CompilationUnit unit;

    private boolean isMinor;

    TreeChange(ProgramElement root) {
        this.root = root;
    }

    public boolean isMinor() {
        return this.isMinor;
    }

    final void setMinor(boolean isMinor) {
        this.isMinor = isMinor;
    }

    public final ProgramElement getChangeRoot() {
        return this.root;
    }

    public abstract NonTerminalProgramElement getChangeRootParent();

    public final CompilationUnit getCompilationUnit() {
        return this.unit;
    }

    final void setCompilationUnit(CompilationUnit cu) {
        this.unit = cu;
    }
}
