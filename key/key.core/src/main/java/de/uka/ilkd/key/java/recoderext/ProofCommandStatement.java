package de.uka.ilkd.key.java.recoderext;

import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.Statement;
import recoder.java.statement.JavaStatement;

/**
 * @author Alexander Weigl
 * @version 1 (11/16/20)
 */
public class ProofCommandStatement extends JavaStatement {
    private final String command;

    public ProofCommandStatement(String command) {
        this.command = command;
    }

    public String getCommand() {
        return command;
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public ProgramElement getChildAt(int i) {
        return null;
    }

    @Override
    public int getChildPositionCode(ProgramElement programElement) {
        return 0;
    }

    @Override
    public boolean replaceChild(ProgramElement programElement, ProgramElement programElement1) {
        return false;
    }

    @Override
    public void accept(SourceVisitor sourceVisitor) {

    }

    @Override
    public Statement deepClone() {
        return null;
    }
}
