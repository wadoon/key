package de.uka.ilkd.key.gui.scripts;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.scripts.actions.GoToNodeAction;
import de.uka.ilkd.key.gui.scripts.actions.ParseScriptAction;
import de.uka.ilkd.key.gui.scripts.actions.ResetScriptAction;
import de.uka.ilkd.key.gui.scripts.actions.StepModeAction;
import de.uka.ilkd.key.macros.scripts.ScriptNode;
import de.uka.ilkd.key.proof.Node;
import org.fife.ui.rtextarea.RTextScrollPane;

import javax.swing.*;
import java.awt.*;
import java.awt.event.MouseEvent;

/**
 * Created by sarah on 2/7/17.
 */
public class ScriptView {


    public ActualScript getCurrentScript() {
        return currentScript;
    }

    private ActualScript currentScript;


    public ScriptTextArea getTextArea() {
        return textArea;
    }

    public MainWindow getMainWindow() {
        return mainWindow;
    }

    public KeYMediator getMediator() {
        return mediator;
    }

    private ScriptTextArea textArea;
    private MainWindow mainWindow;
    private KeYMediator mediator;
    private JPanel view;





    private JToolBar bar;

    public ScriptView(KeYMediator mediator, MainWindow mainWindow){
        this.mainWindow = mainWindow;
        this.mediator = mediator;

        this.currentScript = new ActualScript(mediator);
        initPanel();
    }

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


             // textArea = new RSyntaxTextArea() {
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
    public Component getPanel() {
        return view;
    }

    public void disableReset(){
        bar.getComponent(0).setEnabled(false);

    }

    public void enableReset(){
        bar.getComponent(0).setEnabled(true);

    }


}
