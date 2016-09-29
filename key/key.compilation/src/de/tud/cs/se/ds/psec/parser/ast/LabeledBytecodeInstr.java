package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;

import org.objectweb.asm.Label;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * A labeled bytecode instruction.
 *
 * @author Dominic Scheurer
 */
public class LabeledBytecodeInstr extends Instruction {
    private Label label;
    private TranslationTacletASTElement labeledInstruction;

    /**
     * @param label
     *            The {@link Label} to add to the bytecode.
     * @param labeledInstruction
     *            The {@link TranslationTacletASTElement} that is labeled.
     */
    public LabeledBytecodeInstr(Label label,
            TranslationTacletASTElement labeledInstruction) {
        this.label = label;
        this.labeledInstruction = labeledInstruction;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            TacletApp app, List<TacletASTNode> children) {

        mv.visitLabel(label);
        labeledInstruction.translate(mv, pvHelper, app, children);

    }

}
