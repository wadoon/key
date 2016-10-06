package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * A labeled bytecode instruction.
 *
 * @author Dominic Scheurer
 */
public class LabeledBytecodeInstr extends Instruction {
    private String labelName;
    private Instruction labeledInstruction;

    /**
     * @param labelName
     *            The name of the label. This name has to be unique per
     *            translation definition.
     * @param labeledInstruction
     *            The {@link TranslationTacletASTElement} that is labeled.
     */
    public LabeledBytecodeInstr(String labelName,
            Instruction labeledInstruction) {
        this.labelName = labelName;
        this.labeledInstruction = labeledInstruction;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, TacletApp app, Services services,
            List<TacletASTNode> children) {

        mv.visitLabel(labelManager.getLabelForName(labelName));
        labeledInstruction.translate(mv, pvHelper, labelManager, app, services,
                children);

    }

    /**
     * @return The labeled {@link Instruction} inside this
     *         {@link LabeledBytecodeInstr}.
     */
    Instruction getLabeledInstruction() {
        return labeledInstruction;
    }

}
