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
 * A special {@link Instruction} for popping / pushing loop entry or exit
 * {@link Label}s.
 *
 * @author Dominic Scheurer
 */
public class LoopLabelInstruction extends Instruction {
    public static byte PUSH_LBL = 0;
    public static byte POP_LBL = 1;
    public static byte LOOP_ENTRY = 0;
    public static byte LOOP_EXIT = 1;

    private String labelName;
    private int pushOrPop;
    private int entryOrExit;

    /**
     * Constructs a new loop entry/exit pop/push {@link LoopLabelInstruction}
     * depending on the choice of the parameters.
     * 
     * @param pushOrPop
     *            Either {@link #PUSH_LBL} for pushing or {@link #POP_LBL} for
     *            popping.
     * @param entryOrExit
     *            Either {@link #LOOP_ENTRY} for pushing / popping to/from the
     *            entry label stack or {@link #LOOP_EXIT} for the exit label
     *            stack.
     * @param labelName
     *            The name of the label to push. May be null for
     *            {@link #POP_LBL}.
     */
    public LoopLabelInstruction(int pushOrPop, int entryOrExit,
            String labelName) {
        this.pushOrPop = pushOrPop;
        this.entryOrExit = entryOrExit;
        this.labelName = labelName;
    }

    /**
     * Constructs a new loop entry/exit push {@link LoopLabelInstruction}
     * depending on the choice of the parameters.
     * 
     * @param entryOrExit
     *            Either {@link #LOOP_ENTRY} for pushing / popping to/from the
     *            entry label stack or {@link #LOOP_EXIT} for the exit label
     *            stack.
     * @param labelName
     *            The name of the label to push. May be null for
     *            {@link #POP_LBL}.
     */
    public LoopLabelInstruction(int entryOrExit, String labelName) {
        this(PUSH_LBL, entryOrExit, labelName);
    }

    /**
     * Constructs a new loop entry/exit pop {@link LoopLabelInstruction}
     * depending on the choice of the parameters.
     * 
     * @param entryOrExit
     *            Either {@link #LOOP_ENTRY} for pushing / popping to/from the
     *            entry label stack or {@link #LOOP_EXIT} for the exit label
     *            stack.
     */
    public LoopLabelInstruction(int entryOrExit) {
        this(POP_LBL, entryOrExit, null);
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, RuleInstantiations instantiations,
            Services services, List<TacletASTNode> children) {
        if (pushOrPop == PUSH_LBL) {
            if (entryOrExit == LOOP_ENTRY) {
                pushLoopEntryLabel(labelManager.getLabelForName(labelName));
            } else {
                pushLoopExitLabel(labelManager.getLabelForName(labelName));
            }
        } else {
            if (entryOrExit == LOOP_ENTRY) {
                popLoopEntryLabel();
            } else {
                popLoopExitLabel();
            }
        }
    }

}
