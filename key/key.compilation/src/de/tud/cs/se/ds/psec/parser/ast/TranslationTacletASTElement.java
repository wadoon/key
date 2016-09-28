package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * An element of the translation taclet AST.
 *
 * @author Dominic Scheurer
 */
public abstract class TranslationTacletASTElement implements Opcodes {
    private static final Logger logger = LogManager.getFormatterLogger();

    /**
     * Translates this {@link TranslationTacletASTElement} to bytecode using the
     * given {@link MethodVisitor}. Information about the instantiations of
     * schema variables is taken from the {@link TacletApp}.
     * 
     * @param mv
     *            The {@link MethodVisitor} to use for translating this
     *            {@link TranslationTacletASTElement}.
     * @param pvHelper
     *            A {@link ProgVarHelper} for resolving references to program
     *            variables.
     * @param app
     *            The {@link TacletApp} being used for obtaining instantiations
     *            of schema variables.
     * @param children
     *            The children of in the taclet AST to be taken into account for
     *            translation.
     */
    public abstract void translate(MethodVisitor mv, ProgVarHelper pvHelper, TacletApp app,
            List<TacletASTNode> children);

    /**
     * Returns the value instantiated for the {@link SchemaVariable}
     * <code>sv</code> in the {@link TacletApp} for this {@link TacletASTNode}.
     *
     * @param sv
     *            The name of the {@link SchemaVariable} in the {@link Taclet}.
     * @return The instantiation for <code>sv</code>.
     */
    protected static Object getTacletAppInstValue(TacletApp app, String sv) {
        return app.instantiations()
                .lookupValue(new de.uka.ilkd.key.logic.Name(sv));
    }

    /**
     * Writes a bytecode instruction to load the given integer constant.
     *
     * @param theInt
     *            The integer to load on the stack.
     */
    protected static void intConstInstruction(MethodVisitor mv, int theInt) {
        if (theInt < -1 || theInt > 5) {
            if (theInt >= Byte.MIN_VALUE && theInt <= Byte.MAX_VALUE) {
                mv.visitIntInsn(BIPUSH, theInt);
            }
            else if (theInt >= Short.MIN_VALUE && theInt <= Short.MAX_VALUE) {
                mv.visitIntInsn(SIPUSH, theInt);
            }
            else {
                logger.error(
                        "Constants in full Integer range not yet covered, given: %s",
                        theInt);
                System.exit(1);
            }
        }
        else if (theInt == -1) {
            mv.visitInsn(ICONST_M1);
        }
        else if (theInt == 0) {
            mv.visitInsn(ICONST_0);
        }
        else if (theInt == 1) {
            mv.visitInsn(ICONST_1);
        }
        else if (theInt == 2) {
            mv.visitInsn(ICONST_2);
        }
        else if (theInt == 3) {
            mv.visitInsn(ICONST_3);
        }
        else if (theInt == 4) {
            mv.visitInsn(ICONST_4);
        }
        else if (theInt == 5) {
            mv.visitInsn(ICONST_5);
        }
    }

}
