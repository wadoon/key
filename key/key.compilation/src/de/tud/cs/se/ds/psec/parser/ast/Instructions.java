package de.tud.cs.se.ds.psec.parser.ast;

import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

import org.objectweb.asm.Label;
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

    private Deque<Label> loopEntryLabels = new LinkedList<>();
    private Deque<Label> loopExitLabels = new LinkedList<>();

    /**
     * @param instructions
     *            The list of instructions.
     */
    public Instructions(ArrayList<Instruction> instructions) {
        this.instructions = instructions;
    }

    /**
     * Pushes a loop entry {@link Label} on top of the stack of loop entry
     * {@link Label}s.
     * 
     * @param label
     *            The {@link Label} to push.
     */
    void pushLoopEntryLabel(Label label) {
        loopEntryLabels.push(label);
    }

    /**
     * Pushes a loop entry {@link Label} on top of the stack of loop entry
     * {@link Label}s.
     * 
     * @param label
     *            The {@link Label} to push.
     */
    void pushLoopExitLabel(Label label) {
        loopExitLabels.push(label);
    }

    /**
     * Pops the first loop entry {@link Label} from the stack.
     */
    void popLoopEntryLabel() {
        loopEntryLabels.pop();
    }

    /**
     * Pops the first loop entry {@link Label} from the stack.
     */
    void popLoopExitLabel() {
        loopExitLabels.pop();
    }

    /**
     * Returns, but not removes, the most current loop entry {@link Label}.
     * 
     * @return The most current loop entry {@link Label}.
     */
    Label getUppermostLoopEntryLabel() {
        return loopEntryLabels.peek();
    }

    /**
     * Returns, but not removes, the most current loop exit {@link Label}.
     * 
     * @return The most current loop exit {@link Label}.
     */
    Label getUppermostLoopExitLabel() {
        return loopExitLabels.peek();
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, RuleInstantiations instantiations,
            Services services, List<TacletASTNode> children) {
        instructions.forEach(i -> {
            i.setInstructions(this);
            i.translate(mv, pvHelper, labelManager, instantiations, services,
                    children);
        });
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
