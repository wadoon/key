package de.tud.cs.se.ds.psec.compiler.ast;

import org.objectweb.asm.Label;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * TODO
 *
 * @author Dominic Scheurer
 */
class GreaterThanComparisonSimple extends TacletASTNode {

    /**
     * TODO
     * 
     * @param mv
     * @param pvHelper
     */
    public GreaterThanComparisonSimple(MethodVisitor mv, ProgVarHelper pvHelper, TacletApp app) {
        super(mv, pvHelper, app);
    }

    @Override
    public void compile() {
        LocationVariable locVar = (LocationVariable) getTacletAppInstValue(
                "#lhs");
        Expression expr1 = (Expression) getTacletAppInstValue(
                "#se0");
        Expression expr2 = (Expression) getTacletAppInstValue(
                "#se1");

        loadIntVarOrConst(expr1);
        loadIntVarOrConst(expr2);

        Label l1 = new Label();

        // Comparison
        mv().visitJumpInsn(IF_ICMPLE, l1);

        // "Greater" case: Store 1 (true)
        mv().visitInsn(ICONST_1);

        // Jump to store
        Label l2 = new Label();
        mv().visitJumpInsn(GOTO, l2);

        // "Smaller-equal" case: Store 0 (false)
        mv().visitLabel(l1);
        mv().visitInsn(ICONST_0);

        // Store result of comparison
        mv().visitLabel(l2);
        mv().visitVarInsn(ISTORE, pvHelper().progVarNr(locVar));
        
        compileFirstChild();
    }

}
