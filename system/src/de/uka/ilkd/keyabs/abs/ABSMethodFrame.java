package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramPrefix;

/**
 * Created with IntelliJ IDEA.
 * User: bubel
 * Date: 23.03.13
 * Time: 12:38
 * To change this template use File | Settings | File Templates.
 */
public class ABSMethodFrame extends ABSNonTerminalProgramElement implements IABSStatement, ProgramPrefix, StatementContainer {

    private final ABSExecutionContext executionContext;
    private final ImmutableArray<? extends IABSStatement> body;

    /**
     * contains all program prefix elements below and including itself
     */
    private final ImmutableArray<ProgramPrefix> prefixElementArray;


    public ABSMethodFrame(ABSExecutionContext executionContext,
                          ImmutableArray<? extends IABSStatement> body
                          /* Method Label, Class Label */) {

        this.executionContext = executionContext;
        this.body = body;

        this.prefixElementArray = ABSStatementBlock.computePrefixElements(body, 0, this);
    }


    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnABSMethodFrame(this);
    }

    @Override
    public int getPrefixLength() {
        return prefixElementArray.size();
    }

    @Override
    public ProgramPrefix getPrefixElementAt(int i) {
        return prefixElementArray.get(i);
    }

    @Override
    public ImmutableArray<ProgramPrefix> getPrefixElements() {
        return prefixElementArray;
    }

    @Override
    public PosInProgram getFirstActiveChildPos() {
        return body.size() == 0 ? PosInProgram.TOP :
                PosInProgram.TOP.down(1);
    }

    @Override
    public int getChildCount() {
        return 1 + body.size();
    }

    @Override
    public ProgramElement getChildAt(int index) {
        if (index == 0)
            return executionContext;
        index--;
        return body.get(index);
    }

    @Override
    public int getStatementCount() {
        return body.size();
    }

    @Override
    public Statement getStatementAt(int index) {
        return body.get(index);
    }

    public ABSExecutionContext getExecutionContext() {
        return executionContext;
    }
}
