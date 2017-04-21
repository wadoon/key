package de.uka.ilkd.key.api;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;

import java.util.List;

/**
 * Wrapper for a proof node with utilities methods to
 * Created by S.Grebing
 */
public class ProjectedNode {
    private Node proofNode;

    private ProjectedNode parent;

    private List<ProjectedNode> children;

    private NodeInfo nodeInfo;
    /**Creates the wrapper object for a proof node
     *
     * @param node
     */
    public ProjectedNode(Node node){
        this.proofNode = node;
        this.nodeInfo = node.getNodeInfo();
        
    }

    /**
     * Return the sequent of a proof node
     * @return de.uka.ilkd.key.logic.Sequent s
     */
    public Sequent getSequent(){
        return proofNode.sequent();
    }

    public ProjectedNode getParent(){
        return this.parent;
    }

}
