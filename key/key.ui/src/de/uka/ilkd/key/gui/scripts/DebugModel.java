package de.uka.ilkd.key.gui.scripts;

import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.macros.scripts.ScriptNode;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import java.util.LinkedList;
import java.util.List;

/**
 * Represents the debug state. Stores pointers to the proof and the script.
 * Created by sarah on 2/8/17.
 */
public class DebugModel {

    private ActualScript script;
    private ScriptNode currentPointerToScript;
    private List<ScriptNode> currentState;

    private List<ScriptNode> prevState;
    private ScriptNode prevPointer;

    private Proof assocProofTree;
    private Node pointerToProofTreeNode;
    private List<Node> overallProofState;

    /**
     * Constructor, if Debug starts at root; prev state is here the same as current state
     * @param script
     * @param assocProofTree
     */
    public DebugModel(ActualScript script, Proof assocProofTree){
        this.script = script;
        this.currentPointerToScript = script.getCurrentRoot();
        this.currentState = new LinkedList<ScriptNode>();
        this.overallProofState = new LinkedList<Node>();

        this.currentState.add(currentPointerToScript);
        this.prevState = this.currentState;
        this.prevPointer = this.currentPointerToScript;
        this.assocProofTree = assocProofTree;
        this.pointerToProofTreeNode = assocProofTree.root();
        this.overallProofState.add(pointerToProofTreeNode);
    }

    /**
     * If Debug mode is started in another state than root
     * @param script
     * @param assocProofTree
     * @param nodeToStart
     * @param proofNodeToStart
     */
    public DebugModel(ActualScript script, Proof assocProofTree, ScriptNode nodeToStart, Node proofNodeToStart){
        this.script = script;
        this.assocProofTree = assocProofTree;
        this.pointerToProofTreeNode = proofNodeToStart;
        this.currentPointerToScript = nodeToStart;
        this.currentState = new LinkedList<ScriptNode>();
        this.overallProofState = new LinkedList<Node>();
        this.currentState.add(nodeToStart);
        this.overallProofState.addAll(proofNodeToStart.parent().children());

    }

    private List<ScriptNode> computeParentState(ScriptNode child){
        List<ScriptNode> parentState = new LinkedList<>();
        ScriptNode root = script.getCurrentRoot();
        if(root.getChildren().contains(child)){
            parentState.add(root);
            return parentState;
        }else{
            //recursive
        }



        return parentState;
    }
    /**
     * Get next state according to current state
     * @return
     */
    public List<ScriptNode> getNextScriptState(){
        //save previous state
        this.prevState = this.currentState;
        this.prevPointer = currentPointerToScript;

        this.currentState = currentPointerToScript.getChildren();
        //in case the children contain a scriptNiode with bad from/to pos
        // (open goal node in proof tree; end of debug possibility in script) then change to scriptstate
        List<ScriptNode> children = new LinkedList<ScriptNode>();
        boolean openGoals = false;
        for (ScriptNode scriptNode : this.currentState) {
            if(scriptNode.getFromPos() < 0 || scriptNode.getToPos() <0){
              //  children.add(scriptNode.getParent()); TODO maybe we need this method
                children.add(currentPointerToScript);
                openGoals = true;
            }else{
                children.add(scriptNode);
            }
        }
        if(openGoals){
            this.currentState = children;
        }
        this.currentPointerToScript = this.currentState.get(0);
        return this.currentState;
    }

    /**
     * Set selection pointer if user chooses between different states
     * @param node
     * @throws ScriptException
     */
    public void setCurrentPointerToScript(ScriptNode node) throws ScriptException {
        if(currentState.contains(node)){
            currentPointerToScript = node;
        }else{
            throw new ScriptException("The selected Node "+node.toString()+" is not in the current Debugstate");
        }
    }

    public List<Node> getNextProofTreeNode(){
        overallProofState = pointerToProofTreeNode.children();
        return overallProofState;
    }

    public ScriptNode getCurrentPointerToScript() {
        return currentPointerToScript;
    }

    public List<ScriptNode> getPreviousState(){
        return prevState;
    }
}
