package de.uka.ilkd.key.gui.scripts;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.scripts.actions.*;
import de.uka.ilkd.key.macros.scripts.ScriptNode;
import de.uka.ilkd.key.proof.Node;
import org.fife.ui.rtextarea.RTextScrollPane;

import javax.swing.*;

import java.awt.*;
import java.awt.event.MouseEvent;
import java.util.*;
import java.util.List;

/**
 * fehlt: Persistenz von Scripts, das muss über Datenstruktur und Bookkeeping geregelt werden
 * Created by sarah on 2/7/17.
 */
public class ScriptView {


    public ActualScript getCurrentScript() {
        return currentScript;
    }

    public Component getPanel() {
        return view;
    }

    public ScriptTextArea getTextArea() {
        return textArea;
    }

    public MainWindow getMainWindow() {
        return mainWindow;
    }

    public KeYMediator getMediator() {
        return mediator;
    }


    /**
     * Textarea for script
     */
    private ScriptTextArea textArea;
    private MainWindow mainWindow;
    private KeYMediator mediator;

    /**
     * The script view
     */
    private JPanel view;

    /**
     * The pointer to the script of the currently selected proof
     */
    private ActualScript currentScript;

    public List<ActualScript> getActiveScripts() {
        return activeScripts;
    }

    private List<ActualScript> activeScripts;
    /**
     * Toolbar with buttons for script actions
     */
    private JToolBar bar;


    private ProofListener proofChangedListener;

    public ScriptView(KeYMediator mediator, MainWindow mainWindow){
        this.mainWindow = mainWindow;
        this.mediator = mediator;
        this.activeScripts = new LinkedList<ActualScript>();
        this.currentScript = new ActualScript(mediator);
        this.activeScripts.add(this.currentScript);
        this.proofChangedListener = new ProofListener(this);
        mediator.addKeYSelectionListener(proofChangedListener);
        initPanel();
    }

    /**
     * Initialization of Scriptview
     */
   @SuppressWarnings("serial")
    private void initPanel() {
        view = new JPanel(new BorderLayout());
        {
            bar = new JToolBar();
            bar.setFloatable(false);

            {
                JButton b = new JButton(new ResetScriptAction(this));
                b.setText("R");
                bar.add(b);
            }
            {
                JButton p = new JButton(new ParseScriptAction(this));
                p.setText("P");
                bar.add(p);
            }
            {
                JButton g = new JButton(new GoToNodeAction(this));
                g.setText("G");
                bar.add(g);
            }
            {
                JButton g = new JButton(new StepModeAction(this));
                bar.add(g);
            }
            view.add(bar, BorderLayout.NORTH);
        }

        {
            textArea = new ScriptTextArea() {

                @Override
                public String getToolTipText(MouseEvent e) {
                    int pos = viewToModel(e.getPoint());
                    if (currentScript.getCurrentRoot() != null) {
                        ScriptNode node = getNodeAtPos(currentScript.getCurrentRoot(), pos);
                        if (node != null) {
                            StringBuilder sb = new StringBuilder();
                            if (node.getProofNode() != null)
                                sb.append("\u2192" + node.getProofNode().serialNr());
                            else
                                sb.append("X");
                            if (node.getEncounteredException() != null) {
                                sb.append(" ").append(node.getEncounteredException().getMessage());
                            }
                            return sb.toString();
                        } else {
                            return "no node";
                        }
                    } else {
                        return "not parsed yet";
                    }
                }
            };

            ToolTipManager.sharedInstance().registerComponent(textArea);
            textArea.setPopupMenu(null);
            textArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));
            textArea.setCodeFoldingEnabled(true);
            textArea.setPaintTabLines(true);

            RTextScrollPane scrollpane = new RTextScrollPane(textArea);
            scrollpane.setIconRowHeaderEnabled(true);
            scrollpane.setLineNumbersEnabled(true);

            view.add(scrollpane, BorderLayout.CENTER);

            textArea.addMouseListener(new TextPopupMouseListener(this, currentScript));

        }
    }

    /**
     * Return the ScriptNode at a given position (from the textarea), given the current scriptroot
     * @param node
     * @param pos
     * @return
     */
    public ScriptNode getNodeAtPos(ScriptNode node, int pos) {
        if(node.getFromPos() <= pos && pos < node.getToPos()) {
            return node;
        }

        for (ScriptNode child : node.getChildren()) {
            ScriptNode result = getNodeAtPos(child, pos);
            if(result != null) {
                return result;
            }
        }

        return null;
    }

    /**
     * Show the node in the sequentview which is the starting point for the currently selected proof script command
     * @param pos
     */
    public void goTo(int pos) {
        if(currentScript.getCurrentRoot() == null)
            ExceptionDialog.showDialog(getMainWindow(), new Exception("There is currently no parsed script tree to browse."));

        ScriptNode snode = getNodeAtPos(currentScript.getCurrentRoot(), pos);
        if(snode != null) {
            Node proofNode = snode.getProofNode();
            if(proofNode != null) {
                getMediator().getSelectionModel().setSelectedNode(proofNode);
            }
        }
    }

    /**
     * Disable the reset Button
     */
    public void disableReset(){
        bar.getComponent(0).setEnabled(false);

    }

    /**
     * Enable the reset button
     */
    public void enableReset(){
        bar.getComponent(0).setEnabled(true);

    }


    public void setCurrentScript(ActualScript currentScript) {
        this.currentScript = currentScript;
    }
}
