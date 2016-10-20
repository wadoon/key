package de.tud.cs.se.ds.psec.parser.ast;

import java.util.ArrayList;
import java.util.List;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.uka.ilkd.key.java.Services;

/**
 * Models a set of instructions.
 *
 * @author Dominic Scheurer
 */
public class Instructions extends TranslationTacletASTElement {

    private ArrayList<Instruction> instructions;

    /**
     * @param instructions
     *            The list of instructions.
     */
    public Instructions(ArrayList<Instruction> instructions) {
        this.instructions = instructions;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, RuleInstantiations instantiations,
            Services services, List<TacletASTNode> children) {
        instructions.forEach(i -> i.translate(mv, pvHelper, labelManager,
                instantiations, services, children));
    }

    /**
     * Computes the maximum index of the children called in these
     * {@link Instructions}. This may be used to ignore branches in the SET that
     * should be ignored according to the translation.
     * 
     * @return The maximum index of the children called in these
     *         {@link Instructions}; 0 if no children are called, otherwise the
     *         smallest possible result value is 1.
     */
    int maxIndexOfCalledChildren() {
        return instructions.stream()
                .filter(i -> (i instanceof ChildCall
                        || ((i instanceof LabeledBytecodeInstr)
                                && ((LabeledBytecodeInstr) i)
                                        .getLabeledInstruction() instanceof ChildCall)))
                .map(i -> (i instanceof ChildCall)
                        ? ((ChildCall) i).getChildNo()
                        : ((ChildCall) ((LabeledBytecodeInstr) i)
                                .getLabeledInstruction()).getChildNo())
                .mapToInt(Integer::intValue).max().orElse(0);
    }

}
