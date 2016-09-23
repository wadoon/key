package de.tud.cs.se.ds.psec.compiler.ast;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.Label;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Assignment of the form <code>#lhs = #se0 > #se1;</code>.
 *
 * @author Dominic Scheurer
 */
class EqualityComparisonSimple extends TacletASTNode {
    private static final Logger logger = LogManager.getFormatterLogger();

    /**
     * @see TacletASTNode#TacletASTNode(MethodVisitor, ProgVarHelper, TacletApp)
     */
    public EqualityComparisonSimple(MethodVisitor mv, ProgVarHelper pvHelper, TacletApp app) {
        super(mv, pvHelper, app);
    }

    @Override
    public void compile() {
        logger.trace("Compiling EqualityComparisonSimple");
        
        LocationVariable locVar = (LocationVariable) getTacletAppInstValue(
                "#lhs");
        Expression expr1 = (Expression) getTacletAppInstValue(
                "#se0");
        Expression expr2 = (Expression) getTacletAppInstValue(
                "#se1");

        loadIntVarOrConst(expr1);
        loadIntVarOrConst(expr2);
        
        Label l1 = new Label();
        mv().visitJumpInsn(IF_ICMPNE, l1);
        
        mv().visitInsn(ICONST_1);
        
        Label l2 = new Label();
        mv().visitJumpInsn(GOTO, l2);
        
        mv().visitLabel(l1);
        mv().visitInsn(ICONST_0);
        
        mv().visitLabel(l2);
        mv().visitVarInsn(ISTORE, pvHelper().progVarNr(locVar));
        
        compileFirstChild();
    }

    @Override
    protected int maxNumberOfChildren() {
        return 1;
    }

}
