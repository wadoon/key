package de.tud.cs.se.ds.psec.compiler.ast;

import java.util.ArrayList;
import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Models a symbolic execution taclet and offers a method for translating it
 * into bytecode.
 *
 * @author Dominic Scheurer
 */
public abstract class TacletASTNode implements Opcodes {
    private static final Logger logger = LogManager.getFormatterLogger();

    private List<TacletASTNode> children = new ArrayList<>();
    private MethodVisitor mv;
    private ProgVarHelper pvHelper;
    private TacletApp app;

    /**
     * Recursively translates this node and its children to bytecode.
     */
    public abstract void compile();

    /**
     * TODO
     * 
     * @param mv
     * @param pvHelper
     * @param app
     */
    public TacletASTNode(MethodVisitor mv, ProgVarHelper pvHelper,
            TacletApp app) {
        this.app = app;
        this.mv = mv;
        this.pvHelper = pvHelper;
    }

    /**
     * TODO
     *
     * @return
     */
    protected MethodVisitor mv() {
        return mv;
    }

    /**
     * TODO
     *
     * @return
     */
    protected ProgVarHelper pvHelper() {
        return pvHelper;
    }
    
    /**
     * @return The {@link TacletApp} for this {@link TacletASTNode}.
     */
    protected TacletApp app() {
        return app;
    }

    /**
     * TODO
     *
     * @return
     */
    public List<TacletASTNode> children() {
        return children;
    }
    
    /**
     * TODO
     *
     * @param children
     */
    public void setChildren(List<TacletASTNode> children) {
        this.children = children;
    }
    
    public void addChild(TacletASTNode child) {
        children.add(child);
    }
    
    /**
     * Recursively compiles the first child of this AST node.
     */
    protected void compileFirstChild() {
        if (!children.isEmpty()) {
            children.get(0).compile();
        }
    }

    /**
     * Loads the supplied IntLiteral or (Integer) LocationVariable onto the
     * stack.
     *
     * @param expr
     */
    protected void loadIntVarOrConst(Expression expr) {
        loadIntVarOrConst(expr, false);
    }

    /**
     * Loads the supplied {@link IntLiteral} or (Integer)
     * {@link LocationVariable} onto the stack.
     *
     * @param expr
     */
    protected void loadIntVarOrConst(Expression expr, boolean negative) {
        if (expr instanceof IntLiteral) {
            intConstInstruction((negative ? -1 : 1)
                    * Integer.parseInt(((IntLiteral) expr).toString()));
        } else if (expr instanceof LocationVariable) {
            mv.visitVarInsn(ILOAD, pvHelper.progVarNr((LocationVariable) expr));
        } else {
            logger.error(
                    "Currently not supporting the type %s in assignments, returns etc.",
                    expr.getClass());
        }
    }

    /**
     * Loads the supplied {@link BooleanLiteral} or (boolean)
     * {@link LocationVariable} onto the stack.
     *
     * @param expr
     */
    protected void loadBooleanVarOrConst(Expression expr) {
        if (expr instanceof BooleanLiteral) {
            if (expr.toString().equals("true")) {
                mv.visitInsn(ICONST_1);
            } else {
                mv.visitInsn(ICONST_0);
            }
        } else if (expr instanceof LocationVariable) {
            mv.visitVarInsn(ILOAD, pvHelper.progVarNr((LocationVariable) expr));
        } else {
            logger.error(
                    "Currently not supporting the type %s in assignments, returns etc.",
                    expr.getClass());
        }
    }

    /**
     * TODO
     * 
     * @param acceptedTypesString
     *            TODO
     * @param typeGiven
     */
    protected void unsupportedTypeError(String acceptedTypesString,
            KeYJavaType typeGiven) {
        logger.error(
                "Only %s types considered so far, given: %s, translation %s",
                acceptedTypesString, typeGiven, getClass().getSimpleName());
    }

    /**
     * TODO
     * @param sv
     *
     * @return
     */
    protected Object getTacletAppInstValue(String sv) {
        return app.instantiations()
                .lookupValue(new de.uka.ilkd.key.logic.Name(sv));
    }

    /**
     * TODO
     *
     * @param lit
     */
    private void intConstInstruction(int theInt) {
        if (theInt < -1 || theInt > 5) {
            if (theInt >= Byte.MIN_VALUE && theInt <= Byte.MAX_VALUE) {
                mv.visitIntInsn(BIPUSH, theInt);
            } else if (theInt >= Short.MIN_VALUE && theInt <= Short.MAX_VALUE) {
                mv.visitIntInsn(SIPUSH, theInt);
            } else {
                logger.error(
                        "Constants in full Integer range not yet covered, given: %s",
                        theInt);
            }
        } else if (theInt == -1) {
            mv.visitInsn(ICONST_M1);
        } else if (theInt == 0) {
            mv.visitInsn(ICONST_0);
        } else if (theInt == 1) {
            mv.visitInsn(ICONST_1);
        } else if (theInt == 2) {
            mv.visitInsn(ICONST_2);
        } else if (theInt == 3) {
            mv.visitInsn(ICONST_3);
        } else if (theInt == 4) {
            mv.visitInsn(ICONST_4);
        } else if (theInt == 5) {
            mv.visitInsn(ICONST_5);
        }
    }

}
