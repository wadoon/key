package de.uka.ilkd.key.gui.scripts;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.scripts.actions.GoToNodeAction;
import de.uka.ilkd.key.gui.scripts.actions.ParseScriptAction;
import de.uka.ilkd.key.gui.scripts.actions.ResetScriptAction;
import de.uka.ilkd.key.gui.scripts.actions.StepModeAction;
import de.uka.ilkd.key.macros.scripts.ScriptNode;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rtextarea.RTextScrollPane;

import javax.swing.*;
import java.awt.*;
import java.awt.event.MouseEvent;

/**
 * Created by sarah on 2/7/17.
 */
public class ScriptView {


    public RSyntaxTextArea getTextArea() {
        return textArea;
    }

    public MainWindow getMainWindow() {
        return mainWindow;
    }

    public KeYMediator getMediator() {
        return mediator;
    }

    private RSyntaxTextArea textArea;
    private MainWindow mainWindow;
    private KeYMediator mediator;
    private JPanel view;



    private ActualScript currentScript;



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
            JToolBar bar = new JToolBar();
            bar.setFloatable(false);
            {
                JButton b = new JButton("R");
                b.addActionListener(new ResetScriptAction(this, currentScript));
                bar.add(b);
            }
            {
                JButton p = new JButton("P");
                p.addActionListener(new ParseScriptAction(this, currentScript));
                bar.add(p);
            }
            {
                JButton g = new JButton("G");
                g.addActionListener(new GoToNodeAction(this, currentScript));
                bar.add(g);
            }
            {
                JButton g = new JButton("Step Mode Start");
                g.addActionListener(new StepModeAction(this, currentScript));
                bar.add(g);
            }
            view.add(bar, BorderLayout.NORTH);
        }

        {


              textArea = new RSyntaxTextArea() {
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

    public Component getPanel() {
        return view;
    }


}
