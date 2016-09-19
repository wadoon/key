package de.tud.cs.se.ds.psec.compiler.ast;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.Label;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Splitting rule of the form <code> if(#se) #s0 else #s1</code> or
 * <code> if(#se) #s0</code>. In any case, this rule has two children.
 *
 * @author Dominic Scheurer
 */
class IfElseSplit extends TacletASTNode {
    private static final Logger logger = LogManager.getFormatterLogger();

    /**
     * TODO
     * 
     * @param mv
     * @param pvHelper
     */
    public IfElseSplit(MethodVisitor mv, ProgVarHelper pvHelper,
            TacletApp app) {
        super(mv, pvHelper, app);
    }

    @Override
    public void compile() {
        logger.trace("Compiling IfElseSplit / IfSplit");

        // Note: In some cases, one branch of the split is already closed. In
        // this case, it has no effect on symbolic execution, and we don't
        // compile a split, but just continue translating the children.

        if (children().size() == 2) {
            
            LocationVariable simpleBranchCondition = (LocationVariable) getTacletAppInstValue(
                    "#se");

            mv().visitVarInsn(ILOAD, pvHelper().progVarNr(simpleBranchCondition));

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
            
        } else if (children().size() == 1) {
            
            logger.debug("If(Else)Split with only one child. Might be correct or caused by some bug");
            compileFirstChild();
            
        } else {
            
            logger.error("Unexpected number of children in split node: %s", children().size());
            
        }
        
    }
}
