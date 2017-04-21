package de.uka.ilkd.key.api;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;

import java.util.ArrayList;
import java.util.List;

/**
 * Wrapper for a proof node with utilities methods to
 * Created by S.Grebing
 */
public class ProjectedNode {

    private final Node proofNode;

    private final ProjectedNode parent;

    private final List<ProjectedNode> children;



    /**Creates the wrapper object for a proof node
     *
     * @param node
     * @param parent
     */
    public ProjectedNode(Node node, ProjectedNode parent){
        this.proofNode = node;
        this.children = new ArrayList<>();
        this.parent = parent;
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

    public boolean isRoot(){
        return getParent() == null;
    }

    public NodeInfo getNodeInfo() {
        return proofNode.getNodeInfo();
    }

    //isPseudoNode() <=> proofNode = null
}
