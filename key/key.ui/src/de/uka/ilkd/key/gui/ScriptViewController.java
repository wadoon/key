package de.uka.ilkd.key.gui;

import java.awt.BorderLayout;
import java.awt.Font;
import java.awt.Point;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.IOException;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.ServiceLoader;

import javax.swing.JButton;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JPopupMenu;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JToolBar;
import javax.swing.SwingUtilities;
import javax.swing.ToolTipManager;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.macros.scripts.AbstractCommand;
import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.macros.scripts.ScriptNode;
import de.uka.ilkd.key.macros.scripts.ScriptTreeParser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

/**
 * Created by sarah on 12/20/16.
 */
public class ScriptViewController implements ActionListener{
    private static final Map<String, ProofScriptCommand> COMMANDS = loadCommands();

    private static final Map<String, String> SKIP = Collections.singletonMap("#1", "skip");

  //  private JTextArea textArea;
    private KeYMediator mediator;
    private MainWindow mainWindow;

    private ScriptNode oldroot;
    private Proof associatedProof;

    private JPanel view;
    private JTextArea textArea;

    public ScriptViewController(KeYMediator mediator, MainWindow mainWindow) {
        this.mediator = mediator;
        this.mainWindow = mainWindow;
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
                b.setActionCommand("reset");
                b.addActionListener(this);
                bar.add(b);
            }
            {
                JButton p = new JButton("P");
                p.setActionCommand("parse");
                p.addActionListener(this);
                bar.add(p);
            }
            {
                JButton g = new JButton("G");
                g.setActionCommand("goto");
                g.addActionListener(this);
                bar.add(g);
            }
            view.add(bar, BorderLayout.NORTH);
        }
        {
            textArea = new JTextArea() {
                @Override
                public String getToolTipText(MouseEvent e) {
                    int pos = viewToModel(e.getPoint());
                    if (oldroot != null) {
                        ScriptNode node = getNodeAtPos(oldroot, pos);
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

            textArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));
            view.add(new JScrollPane(textArea), BorderLayout.CENTER);
            textArea.addMouseListener(new MouseAdapter() {
                @Override
                public void mouseClicked(MouseEvent e) {
                    if(SwingUtilities.isRightMouseButton(e)) {
                        int pos = textArea.viewToModel(e.getPoint());
                        textPopup(e.getPoint(), pos);
                    }
                }
            });
        }
    }

    public JPanel getPanel() {
        return view;
    }


    protected void textPopup(Point p, final int pos) {
        final ScriptNode node;
        if(oldroot != null) {
            node = getNodeAtPos(oldroot, pos);
        } else {
            node = null;
        }

        JPopupMenu pm = new JPopupMenu();
        {
            JMenuItem m = new JMenuItem("Show node exception");
            if (node == null || node.getEncounteredException() == null) {
                m.setEnabled(false);
            }
            m.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    ExceptionDialog.showDialog(mainWindow, node.getEncounteredException());
                }
            });
            pm.add(m);
        }
        {
            // TODO Implement me!
            JMenuItem m = new JMenuItem("Reparse from here");
            // if (node == null)
            {
                m.setEnabled(false);
            }
            pm.add(m);
        }
        {
            JMenuItem m = new JMenuItem("Show in proof tree");
            if (node == null) {
                m.setEnabled(false);
            }
            m.addActionListener(new ActionListener() {
                @Override
                public void actionPerformed(ActionEvent e) {
                    textArea.setCaretPosition(pos);
                    goTo();
                }
            });
            pm.add(m);
        }
        pm.addSeparator();
        {
            JMenuItem m = new JMenuItem("(Re)parse");
            if (associatedProof == null) {
                m.setEnabled(false);
            }
            m.addActionListener(new ActionListener() {
                @Override
                public void actionPerformed(ActionEvent e) {
                    try {
                        parse();
                    } catch (Exception ex) {
                        ExceptionDialog.showDialog(mainWindow, ex);
                    }
                }
            });
            pm.add(m);
        }
        {
            JMenuItem m = new JMenuItem("(Re)connect to proof");
            m.addActionListener(new ActionListener() {
                @Override
                public void actionPerformed(ActionEvent e) {
                    reset();
                }
            });
            pm.add(m);
        }
        pm.show(textArea, p.x, p.y);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        try {
            switch(e.getActionCommand()) {
                case "reset":
                    reset();
                    break;
                case "parse":
                    parse();
                    break;
                case "goto":
                    goTo();
                    break;
                default: throw new Error();
            }
        } catch (Exception ex) {
            ExceptionDialog.showDialog(mainWindow, ex);
        }
    }

    private void reset() {
        associatedProof = mediator.getSelectedProof();
        oldroot = null;
    }

    private void parse() throws IOException, ScriptException, InterruptedException {
        if(associatedProof != mediator.getSelectedProof())
            throw new ScriptException("wrong proof selcted");

        ScriptNode newroot = ScriptTreeParser.parse(new StringReader(textArea.getText()));
        newroot.setProofNode(associatedProof.root());

        try {
            mediator.stopInterface(true);
            if(oldroot != null) {
                oldroot.dump(0);
                newroot.dump(0);
            }
            compareAndAct(newroot, oldroot);
            oldroot = newroot;
        } finally {
            mediator.startInterface(true);
        }
    }

    private void compareAndAct(ScriptNode newnode, ScriptNode oldnode) throws ScriptException, InterruptedException {

        if(oldnode != null && newnode.getCommand().equals(oldnode.getCommand())) {
            Iterator<ScriptNode> nIt = newnode.getChildren().iterator();
            Iterator<ScriptNode> oIt = oldnode.getChildren().iterator();
            while(oIt.hasNext() && nIt.hasNext()) {
                ScriptNode n = nIt.next();
                ScriptNode o = oIt.next();
                n.setProofNode(o.getProofNode());
                compareAndAct(n, o);
            }
            while(oIt.hasNext()) {
                // old node has more than new node: prune these
                mediator.setBack(oIt.next().getProofNode());
            }
            while(nIt.hasNext()) {
                // XXX This is not good and will definitely fail.
                // new node has more than old node: go into these too.
                compareAndAct(nIt.next(), null);
            }

        } else {

            Node node = newnode.getProofNode();
            if(node == null) {
                node = oldnode.getProofNode();
            }
            mediator.setBack(node);

            Map<String, String> argMap = newnode.getCommand();
            String name = argMap.get("#1");
            if(name == null) {
                throw new ScriptException("No command");
            }

            ProofScriptCommand command = COMMANDS.get(name);
            if(command == null) {
                throw new ScriptException("Unknown command " + name);
            }

            HashMap<String, Object> state = new HashMap<String, Object>();
            state.put(AbstractCommand.GOAL_KEY, node);
            try {
                command.execute(mediator.getUI(), associatedProof, argMap, state);
            } catch (ScriptException e) {
                associatedProof.pruneProof(node);
                newnode.setEncounteredException(e);
                newnode.clearChildren();
            }

            java.util.List<Node> leaves = new ArrayList<Node>();
            findLeaves(node, leaves);
            leaves.remove(node);
            java.util.List<ScriptNode> children = newnode.getChildren();

            //            if(children.size() != 0 && children.size() != leaves.size()) {
            //                throw new ScriptException("Command " + argMap.get("#literal") +
            //                        " requires " + leaves.size() +
            //                        " children, but received " + children.size());
            //            }

            if(children.size() > leaves.size()) {
                throw new ScriptException("Command " + argMap.get("#literal") +
                        " requires " + leaves.size() +
                        " children, but received " + children.size());
            }

            while(children.size() < leaves.size()) {
                // Adding phantom skip nodes ...
                children.add(new ScriptNode(SKIP, -1, -1));
            }

            for(int i=0; i < children.size(); i++) {
                children.get(i).setProofNode(leaves.get(i));
            }

            for (ScriptNode child : children) {
                compareAndAct(child, null);
            }
        }

    }

    private void findLeaves(Node node, java.util.List<Node> leaves) {

        while(node.childrenCount() == 1) {
            node = node.child(0);
        }

        if(node.leaf() && !node.isClosed())
            leaves.add(node);

        for (Node child : node.children()) {
            findLeaves(child, leaves);
        }
    }

    private void goTo() {
        int pos = textArea.getCaretPosition();
        if(oldroot == null)
            ExceptionDialog.showDialog(mainWindow, new Exception("There is currently no parsed script tree to browse."));
        ScriptNode snode = getNodeAtPos(oldroot, pos);
        if(snode != null) {
            Node proofNode = snode.getProofNode();
            if(proofNode != null) {
                mediator.getSelectionModel().setSelectedNode(proofNode);
            }
        }
    }

    private ScriptNode getNodeAtPos(ScriptNode node, int pos) {
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

    private static Map<String, ProofScriptCommand> loadCommands() {
        Map<String, ProofScriptCommand> result = new HashMap<String, ProofScriptCommand>();
        ServiceLoader<ProofScriptCommand> loader = ServiceLoader.load(ProofScriptCommand.class);

        for (ProofScriptCommand cmd : loader) {
            result.put(cmd.getName(), cmd);
        }

        return result;
    }

}
