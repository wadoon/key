package de.tud.cs.se.ds.psec.compiler.taclet_translation;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Models a symbolic execution taclet and offers a method for translating it
 * into bytecode.
 *
 * @author Dominic Scheurer
 */
public abstract class TacletTranslation implements Opcodes {
    private static final Logger logger = LogManager.getFormatterLogger();
    
    private MethodVisitor mv;
    private ProgVarHelper pvHelper;

    /**
     * Translates the given {@link TacletApp} to bytecode.
     *
     * @param app
     *            The {@link TacletApp} to translate.
     * @return <code>true</code> iff the {@link TacletApp} should terminate the
     *         translation, i.e. it is some kind of return statement.
     */
    public abstract boolean compile(TacletApp app);

    /**
     * TODO
     * 
     * @param mv
     * @param pvHelper
     */
    public TacletTranslation(MethodVisitor mv, ProgVarHelper pvHelper) {
        this.mv = mv;
        this.pvHelper = pvHelper;
    }

    /**
     * TODO
     *
     * @return
     */
    public MethodVisitor mv() {
        return mv;
    }

    /**
     * TODO
     *
     * @return
     */
    public ProgVarHelper pvHelper() {
        return pvHelper;
    }

    /**
     * Loads the supplied IntLiteral or (Integer) LocationVariable onto the
     * stack.
     *
     * @param expr
     */
    protected void loadIntVarOrConst(Expression expr) {
        if (expr instanceof IntLiteral) {
            intConstInstruction((IntLiteral) expr);
        } else if (expr instanceof LocationVariable) {
            mv.visitVarInsn(ILOAD, pvHelper.progVarNr((LocationVariable) expr));
        } else {
            System.err.println(
                    "[WARNING] Currently not supporting the type "
                            + expr.getClass()
                            + " in assignments, returns etc.");
        }
    }
    
    /**
     * TODO
     *
     * @param typeGiven
     */
    protected void onlyIntegerTypesError(KeYJavaType typeGiven) {
        logger.error("Only integer types considered so far, given: %s", typeGiven);
    }

    /**
     * TODO
     *
     * @param lit
     */
    private void intConstInstruction(IntLiteral lit) {
        int theInt = Integer.parseInt(lit.toString());

        if (theInt < -1 || theInt > 5) {
            if (theInt >= Byte.MIN_VALUE && theInt <= Byte.MAX_VALUE) {
                mv.visitIntInsn(BIPUSH, theInt);
            } else if (theInt >= Short.MIN_VALUE && theInt <= Short.MAX_VALUE) {
                mv.visitIntInsn(SIPUSH, theInt);
            } else {
                System.err.println(
                        "[WARNING] Constants in full Integer range not yet covered, given: "
                                + theInt);
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

    /**
     * TODO
     *
     * @param app
     * @param sv
     * @return
     */
    public static Object getTacletAppInstValue(TacletApp app, String sv) {
        return app.instantiations()
                .lookupValue(new de.uka.ilkd.key.logic.Name(sv));
    }

}
