package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.statement.JavaStatement;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;

import java.io.IOException;

/**
 * @author Alexander Weigl
 * @version 1 (11/16/20)
 */
public class ProofCommandStatement extends JavaStatement {
    private final String command;

    public ProofCommandStatement(String command) {
        this.command = command;
    }

    public ProofCommandStatement(String command, PositionInfo positionInfo) {
        super(positionInfo);
        this.command = command;
    }

    public ProofCommandStatement(ExtList changeList) {
        super(changeList);
        command = changeList.get(String.class);
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        return null;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnProofCommand(this);
    }

    @Override
    public void prettyPrint(PrettyPrinter w) throws IOException {
        w.printProofCommand(this);
    }

    public String getCommand() {
        return command;
    }
}
