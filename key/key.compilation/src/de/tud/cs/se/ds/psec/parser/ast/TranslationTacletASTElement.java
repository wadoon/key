package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.Label;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import de.tud.cs.se.ds.psec.compiler.GlobalLabelHelper;
import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.parser.exceptions.UnsupportedFeatureException;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.tud.cs.se.ds.psec.util.Utilities;
import de.uka.ilkd.key.java.Services;
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
     * @param globalLabelHelper TODO
     * @param labelManager
     *            The {@link UniqueLabelManager} for keeping track of the
     *            connection between {@link Label} names and objects.
     * @param instantiations
     *            The {@link RuleInstantiations} for retrieving instantiations
     *            for, e.g., {@link SchemaVariable}s.
     * @param children
     *            The children of in the taclet AST to be taken into account for
     *            translation.
     */
    public abstract void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            GlobalLabelHelper globalLabelHelper, UniqueLabelManager labelManager,
            RuleInstantiations instantiations, Services services, List<TacletASTNode> children);

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
            } else if (theInt >= Short.MIN_VALUE && theInt <= Short.MAX_VALUE) {
                mv.visitIntInsn(SIPUSH, theInt);
            } else {
                String message = Utilities.format(
                        "Constants in full Integer range not yet covered, given: %s",
                        theInt);
                logger.error(message);

                throw new UnsupportedFeatureException(message);
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
