package de.uka.ilkd.key.nui.util;

import de.uka.ilkd.key.core.InterruptListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.DefaultTaskStartedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.TaskFinishedInfo;
import de.uka.ilkd.key.proof.TaskStartedInfo.TaskKind;
import de.uka.ilkd.key.util.Debug;
import javafx.concurrent.Task;

/**
 * Copied from ProofMacroWorker and adapted to JavaFX.
 * <p>
 * The Class ProofMacroWorker is a worker for the application of proof macros.
 *
 * It decouples {@link ProofMacro proof macros} from the GUI event thread. It
 * registers with the {@link KeYMediator} to receive Stop-Button events.
 * 
 * @author Nils Muzzulini
 * @see de.uka.ilkd.key.gui.ProofMacroWorker
 * @version 1.0
 */
public class ProofMacroWorker extends Task<Void> implements InterruptListener {

    /**
     * This flag decides whether after a macro an open is selected or not. If
     * the macro closed all goals under the current pio, selection remains where
     * it was.
     */
    private static final boolean SELECT_GOAL_AFTER_MACRO = Boolean
            .parseBoolean(System.getProperty("key.macro.selectGoalAfter", "true"));

    /**
     * The macro which is to be executed
     */
    private final ProofMacro macro;

    /**
     * The mediator of the environment
     */
    private final KeYMediator mediator;

    /**
     * This position may be null if no subterm selected
     */
    private final PosInOccurrence posInOcc;

    /**
     * Instantiates a new proof macro worker.
     *
     * @param macro
     *            the macro, not null
     * @param mediator
     *            the mediator, not null
     * @param posInOcc
     *            the position, possibly null
     */
    public ProofMacroWorker(ProofMacro macro, KeYMediator mediator, PosInOccurrence posInOcc) {
        assert macro != null;
        assert mediator != null;
        this.macro = macro;
        this.mediator = mediator;
        this.posInOcc = posInOcc;
    }
    
    @Override
    public void interruptionPerformed() {
        cancel(true);
    }

    @Override
    protected void done() {
        synchronized (macro) {
            if (SELECT_GOAL_AFTER_MACRO) {
                selectOpenGoalBelow();
            }
            mediator.setInteractive(true);
            mediator.startInterface(true);
            mediator.removeInterruptedListener(this);
        }
    }

    /**
     * Select a goal below the currently selected node. Does not do anything if
     * that is not available. Only enabled goals are considered.
     */
    private void selectOpenGoalBelow() {
        Node selectedNode = mediator.getSelectedNode();
        for (Goal g : selectedNode.proof().openEnabledGoals()) {
            Node n = g.node();
            while (n != null) {
                if (n == selectedNode) {
                    mediator.getSelectionModel().setSelectedGoal(g);
                    return;
                }
                n = n.parent();
            }
        }
    }

    @Override
    protected Void call() throws Exception {
        final ProverTaskListener ptl = mediator.getUI();
        Node selectedNode = mediator.getSelectedNode();
        Proof selectedProof = selectedNode.proof();
        TaskFinishedInfo info = ProofMacroFinishedInfo.getDefaultInfo(macro, selectedProof);
        ptl.taskStarted(new DefaultTaskStartedInfo(TaskKind.Macro, macro.getName(), 0));
        try {
            synchronized (macro) {
                info = macro.applyTo(mediator.getUI(), selectedNode, posInOcc, ptl);
            }
        }
        catch (final InterruptedException exception) {
            Debug.out("Proof macro has been interrupted:");
            Debug.out(exception);
        }
        catch (final Exception exception) {
            // This should actually never happen.
            exception.printStackTrace();
        }
        finally {
            ptl.taskFinished(info);
        }
        return null;
    }
}