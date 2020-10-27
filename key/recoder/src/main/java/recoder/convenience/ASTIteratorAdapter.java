package recoder.convenience;

import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;

public class ASTIteratorAdapter implements ASTIteratorListener {
    public void enteringNode(ASTIterator it, ProgramElement node) {
    }

    public void leavingNode(ASTIterator it, ProgramElement node) {
    }

    public int enterChildren(ASTIterator it, NonTerminalProgramElement thisNode) {
        return 2;
    }

    public boolean enterChildNode(ASTIterator it, NonTerminalProgramElement thisNode, ProgramElement childNode) {
        return true;
    }

    public void returnedFromChildNode(ASTIterator it, NonTerminalProgramElement thisNode, ProgramElement childNode) {
    }
}
