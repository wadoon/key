package de.uka.ilkd.key.gui;

import java.awt.BorderLayout;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.ServiceLoader;

import javax.swing.JButton;
import javax.swing.JPanel;
import javax.swing.JTextArea;
import javax.swing.JToolBar;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.macros.scripts.AbstractCommand;
import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.macros.scripts.ScriptNode;
import de.uka.ilkd.key.macros.scripts.ScriptTreeParser;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

public class ScriptView extends JPanel implements ActionListener {

    private static final Map<String, ProofScriptCommand> COMMANDS = loadCommands();

    private static final Map<String, String> SKIP = Collections.singletonMap("#1", "skip");
    
    private JTextArea textArea;
    private KeYMediator mediator;
    private MainWindow mainWindow;
    
    private ScriptNode oldroot;
    private Proof associatedProof;
    
    public ScriptView(KeYMediator mediator, MainWindow mainWindow) {
        this.mediator = mediator;
        this.mainWindow = mainWindow;
        init();
    }

    private void init() {
        setLayout(new BorderLayout());
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
                JButton b = new JButton("P");
                b.setActionCommand("parse");
                b.addActionListener(this);
                bar.add(b);
            }
            {
                JButton b = new JButton("G");
                b.setActionCommand("goto");
                b.addActionListener(this);
                bar.add(b);
            }
            add(bar, BorderLayout.NORTH);
        }
        {
            textArea = new JTextArea();
            textArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));
            add(textArea, BorderLayout.CENTER);
        }
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
            
            Goal g = null;
            for(Goal g2 : associatedProof.openGoals()) {
                if(g2.node() == node)
                { g = g2; break; } 
            }
            
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
                ExceptionDialog.showDialog(mainWindow, new Exception("intermed. local error:" + e.getMessage(), e));
                associatedProof.pruneProof(node);
                newnode.clearChildren();
            }
            
            List<Node> leaves = new ArrayList<Node>();
            findLeaves(node, leaves);
            leaves.remove(node);
            List<ScriptNode> children = newnode.getChildren();
            
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

    private void findLeaves(Node node, List<Node> leaves) {

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
        goTo(oldroot, pos);
    }

    private void goTo(ScriptNode node, int pos) {
        if(node.getFromPos() <= pos && pos < node.getToPos()) {
            Node proofNode = node.getProofNode();
            if(proofNode != null) {
                mediator.getSelectionModel().setSelectedNode(proofNode);
            }
            return;
        }
        
        for (ScriptNode child : node.getChildren()) {
            goTo(child, pos);
        }
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
