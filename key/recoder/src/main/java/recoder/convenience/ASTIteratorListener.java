package recoder.convenience;

import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;

public interface ASTIteratorListener {
    int ENTER_NONE = 0;

    int ENTER_SOME = 1;

    int ENTER_ALL = 2;

    void enteringNode(ASTIterator paramASTIterator, ProgramElement paramProgramElement);

    void leavingNode(ASTIterator paramASTIterator, ProgramElement paramProgramElement);

    int enterChildren(ASTIterator paramASTIterator, NonTerminalProgramElement paramNonTerminalProgramElement);

    boolean enterChildNode(ASTIterator paramASTIterator, NonTerminalProgramElement paramNonTerminalProgramElement, ProgramElement paramProgramElement);

    void returnedFromChildNode(ASTIterator paramASTIterator, NonTerminalProgramElement paramNonTerminalProgramElement, ProgramElement paramProgramElement);
}
