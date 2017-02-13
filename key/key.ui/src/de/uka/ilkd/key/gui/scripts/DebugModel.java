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

    /**
     * Parsed Script that will be debugged
     */
    private ActualScript script;

    /**
     * Highlighted and selected ScriptNode
     */
    private ScriptNode currentPointerToScript;

    /**
     * Debugstate in focus (all siblings of selected ScriptNode including selected Node)
     */
    private List<ScriptNode> currentState;

    /**
     * Previous Debugstate (maybe null if current is root)
     */
  //  private List<ScriptNode> prevState;

    /**
     * Pointer to parent ScriptNode (if null, then current ScriptNode is root)
     */
  //  private ScriptNode prevPointer;

    /**
     * Associated Proof Tree that resulted from executing teh proof script
     */
    private Proof assocProofTree;

    /**
     * Pointer to Node in the proof tree of current
     */
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
     //   this.overallProofState = new LinkedList<Node>();

        this.currentState.add(currentPointerToScript);
    //    this.prevState = null;
     //   this.prevPointer = null;
        this.assocProofTree = assocProofTree;
        this.pointerToProofTreeNode = assocProofTree.root();
   //     this.overallProofState.add(pointerToProofTreeNode);
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
 //       this.overallProofState = new LinkedList<Node>();
        this.currentState.add(nodeToStart);
 //       this.overallProofState.addAll(proofNodeToStart.parent().children());

    }


    public void computeNextState(){
        this.currentState = computeNextState_1();
    }

    public void computePrevState(){
        this.currentState = computeParentState();
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

/*    public List<Node> getNextProofTreeNode(){
        overallProofState = pointerToProofTreeNode.children();
        return overallProofState;
    }*/

    public ScriptNode getCurrentPointerToScript() {
        return currentPointerToScript;
    }

    /**
     * Computes the parent state and sets the currentpointer to the parent
     * @return
     */
    private List<ScriptNode> computeParentState(){
        ScriptNode currentPointer = this.currentPointerToScript;
        ScriptNode parentPointer = currentPointer.getParent();
        List<ScriptNode> state;
        if(parentPointer != null){
            ScriptNode parentOfParent = parentPointer.getParent();
            if (parentPointer.getParent() != null) {
                state = parentOfParent.getChildren();
            }else{
                state = new LinkedList<>();
                state.add(parentPointer);
            }
        }else{
            state = currentState;
        }
        this.currentPointerToScript = parentPointer;
        return state;
    }


    private List<ScriptNode> computeNextState_1(){
        ScriptNode currentPointer = this.currentPointerToScript;
        List<ScriptNode> nextState;
        if (currentPointer == null){
            nextState = new LinkedList();
            nextState.add(script.getCurrentRoot());
            this.currentPointerToScript = script.getCurrentRoot();
            return nextState;
        }else{
            nextState = currentPointer.getChildren();
        }
        //in case the children contain a scriptNode with bad from/to pos
        // (open goal node in proof tree; end of debug possibility in script) then change to scriptstate

        List<ScriptNode> children = new LinkedList<ScriptNode>();
        boolean openGoals = false;
        for (ScriptNode scriptNode : nextState) {
            //in case a SKIP Node is in the next state
            if(scriptNode.getFromPos() < 0 || scriptNode.getToPos() <0){

                children.add(currentPointer);
                openGoals = true;
            }else{
                children.add(scriptNode);
            }
        }
        if(openGoals){
            nextState = children;
        }

        this.currentPointerToScript = nextState.get(0);
        return nextState;
    }
    public List<ScriptNode> getCurrentState() {
        return this.currentState;
    }



}
