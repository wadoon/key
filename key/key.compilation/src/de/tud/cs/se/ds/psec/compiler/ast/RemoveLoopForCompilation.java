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

        // Note: In some cases, one branch of the split is already closed. In
        // this case, it has no effect on symbolic execution, and we don't
        // compile a split, but just continue translating the children.

        LocationVariable simpleLoopCondition =
                (LocationVariable) getTacletAppInstValue(
                        "#se");
        
        //TODO: Rest is copied from IfElse

        mv().visitVarInsn(ILOAD,
                pvHelper().progVarNr(simpleLoopCondition));

        Label l0 = new Label();
        mv().visitJumpInsn(IFEQ, l0);

        // then-part. Don't have to GOTO the block after the if since state
        // merging is not yet incorporated.
        // XXX Make sure that the code doesn't reach the ELSE part if no
        // explicit return statement is there (void methods)

        children().get(0).compile();

        // else-part.
        mv().visitLabel(l0);
        children().get(1).compile();

    }
}
