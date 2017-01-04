package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;

import org.objectweb.asm.Label;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.uka.ilkd.key.java.Services;

/**
 * A labeled bytecode instruction.
 *
 * @author Dominic Scheurer
 */
public class LabeledBytecodeInstr extends Instruction {
    private LabelNameOrNameDecl labelName;
    private Instruction labeledInstruction;

    /**
     * @param labelName
     *            The name of the label. This name has to be unique per
     *            translation definition.
     * @param labeledInstruction
     *            The {@link TranslationTacletASTElement} that is labeled.
     */
    public LabeledBytecodeInstr(LabelNameOrNameDecl labelName,
            Instruction labeledInstruction) {
        this.labelName = labelName;
        this.labeledInstruction = labeledInstruction;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, RuleInstantiations instantiations, Services services,
            List<TacletASTNode> children) {

        String name = labelName.getName(instantiations);
        Label lbl = labelName.isExplicitName()
                ? labelManager.getLabelForName(name) : getGlobalLabel(name);

        //TODO Visit label iff not visited already
        mv.visitLabel(lbl);
        labeledInstruction.translate(mv, pvHelper, labelManager, instantiations, services,
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
