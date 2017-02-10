package de.uka.ilkd.key.gui.scripts;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.macros.scripts.*;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import java.io.IOException;
import java.io.StringReader;
import java.util.*;

/**
 * Created by sarah on 2/7/17.
 */
public class ActualScript {
    private static final Map<String, ProofScriptCommand> COMMANDS = loadCommands();

    private static final Map<String, String> SKIP = Collections.singletonMap("#1", "skip");

    KeYMediator mediator;

    /**
     * The script's underlying proof
     */
    private Proof associatedProof;

    public String getTextReprOfScript() {
        return textReprOfScript;
    }

    private String textReprOfScript;

    /**
     * The data structure representing the script as tree
     */
    private ScriptNode currentRoot;

    private Map<String, String> currentArgMap;

    public Proof getAssociatedProof() {
        return associatedProof;
    }

    public void setAssociatedProof(Proof associatedProof) {
        this.associatedProof = associatedProof;
    }

    public ScriptNode getCurrentRoot() {
        return currentRoot;
    }

    public void setCurrentRoot(ScriptNode currentRoot) {
        this.currentRoot = currentRoot;
    }

    public ActualScript(KeYMediator mediator){
        this.mediator = mediator;
        this.associatedProof = mediator.getSelectedProof();
        this.currentArgMap = new HashMap<String, String>();
        this.currentRoot = null;
        this.textReprOfScript = "";
    }

    /**
     * Load all available scriptcommands
     * @return
     */
    private static Map<String, ProofScriptCommand> loadCommands() {
        Map<String, ProofScriptCommand> result = new HashMap<String, ProofScriptCommand>();
        ServiceLoader<ProofScriptCommand> loader = ServiceLoader.load(ProofScriptCommand.class);

        for (ProofScriptCommand cmd : loader) {
            result.put(cmd.getName(), cmd);
        }

        return result;
    }

    public void parse(StringReader reader) throws IOException, ScriptException, InterruptedException {

        if (associatedProof != mediator.getSelectedProof())
            throw new ScriptException("wrong proof selected");

        ScriptNode newroot = ScriptTreeParser.parse(reader);

        newroot.setProofNode(associatedProof.root());

        try {
            mediator.stopInterface(true);
            if (currentRoot != null) {
                currentRoot.dump(0);
                newroot.dump(0);
            }
            compareAndAct(newroot, currentRoot);
            this.setCurrentRoot(newroot);

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
                getPaths(n.getProofNode());
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


            List<Node> leaves = act(newnode);
            List<ScriptNode> children = newnode.getChildren();

            //            if(children.size() != 0 && children.size() != leaves.size()) {
            //                throw new ScriptException("Command " + argMap.get("#literal") +
            //                        " requires " + leaves.size() +
            //                        " children, but received " + children.size());
            //            }

            if(children.size() > leaves.size()) {
                throw new ScriptException("Command " +
                        this.currentArgMap.get("#literal") +
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

    /**
     * Retrieve Path in Proof tree for a given node up to the root of the tree
     * @param node
     * @return
     */
    public List<Node> getPaths(Node node){
        LinkedList<Node> nodes = new LinkedList<>();
        nodes.add(node);
        int i = node.serialNr();
        Node tempN = node;
        Node tempParent = node.parent();
        while(i != 0 && tempParent != null){
            nodes.add(tempParent);
            i = extractParentNr(tempN);
            tempN= tempParent;
            tempParent = tempN.parent();
        }
        return nodes;

    }

    private int extractParentNr(Node n){
        if(n.parent() != null) return n.parent().serialNr();
        else return 0;
    }

    private List<Node> act(ScriptNode newnode) throws ScriptException, InterruptedException{

        Node node = newnode.getProofNode();
        if(node == null) {
            throw new ScriptException("No Matching Proof Node found");
        }
        mediator.setBack(node);

        Map<String, String> argMap = newnode.getCommand();
        String name = argMap.get("#1");
        if(name == null) {
            throw new ScriptException("No command");
        }

        ProofScriptCommand command = COMMANDS.get(name);


        //assume command may be a macro call
        if(command == null && !name.equals("skip")){

            name = "macro";
            argMap.put("#2", argMap.get("#1"));
            argMap.put("#1", name);
            command = COMMANDS.get(name);

            String lit = argMap.get("#literal");
            argMap.put("#literal", "macro "+lit);
            this.currentArgMap = argMap;

        }

        //hier Behandlung von skip, dass execute nicht auf skip angewandt wird
        HashMap<String, Object> state = new HashMap<String, Object>();
        state.put(AbstractCommand.GOAL_KEY, node);
        try {
            if(!name.equals("skip")) {
                command.execute(mediator.getUI(), getAssociatedProof(), argMap, state);
            }

        } catch (ScriptException e) {
            associatedProof.pruneProof(node);
            newnode.setEncounteredException(e);
            newnode.clearChildren();
        }

        List<Node> leaves = new ArrayList<Node>();
        findLeaves(node, leaves);
        leaves.remove(node);
        //  getPaths(node);
        return leaves;

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


    public void setTextReprOfScript(String textReprOfScript) {
        this.textReprOfScript = textReprOfScript;
    }
}
