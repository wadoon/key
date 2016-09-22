package de.tud.cs.se.ds.psec.compiler.ast;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.Label;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Refers to special taclet removing a while loop with simple loop expression
 * for the purpose of compilation. The first child branch contains the loop
 * body, the second one the code after the loop.
 * <p>
 * The find part of the taclet is of the form:<br/>
 * <code>while(#se) #s #slist</code>
 *
 * @author Dominic Scheurer
 */
class RemoveLoopForCompilation extends TacletASTNode {
    private static final Logger logger = LogManager.getFormatterLogger();

    /**
     * @see TacletASTNode#TacletASTNode(MethodVisitor, ProgVarHelper, TacletApp)
     */
    public RemoveLoopForCompilation(MethodVisitor mv, ProgVarHelper pvHelper,
            TacletApp app) {
        super(mv, pvHelper, app);
    }

    @Override
    public void compile() {
        logger.trace("Compiling removeLoopForCompilation");

        LocationVariable simpleLoopCondition = (LocationVariable) getTacletAppInstValue(
                "#se");

        Label l1 = new Label();
        Label l2 = new Label();

        mv().visitJumpInsn(GOTO, l1);
        mv().visitLabel(l2);

        children().get(0).compile();

        mv().visitLabel(l1);
        mv().visitVarInsn(ILOAD, pvHelper().progVarNr(simpleLoopCondition));
        mv().visitJumpInsn(IFNE, l2);

        if (children().size() < 2) {
            // This loop is the last statement of a void method (otherwise, we
            // have some problem), so we add a return statement
            new MethodCallEmptyReturn(mv(), pvHelper(), null).compile();
        } else {
            children().get(1).compile();
        }
    }

    @Override
    protected int maxNumberOfChildren() {
        return 2;
    }
}
