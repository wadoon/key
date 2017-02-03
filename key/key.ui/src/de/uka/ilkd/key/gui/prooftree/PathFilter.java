package de.uka.ilkd.key.gui.prooftree;

import de.uka.ilkd.key.proof.Node;

import javax.swing.tree.TreeNode;
import java.util.Enumeration;
import java.util.LinkedList;
import java.util.List;

/**
 * Filter Proof Tree View acc. to nodes List
 * Created by sarah on 12/23/16.
 */
public class PathFilter extends ProofTreeViewFilter.NodeFilter{
    boolean active;

    public void setNodes(List<Node> nodes) {
        this.nodes = nodes;
        this.active = false;
    }

    List<Node> nodes;
        public PathFilter(List<Node> nodes){
            if (nodes == null) {
                this.nodes = new LinkedList<>();

            }else{
                this.nodes = nodes;
            }
        }
        @Override
        public boolean isActive() {
            return this.active;
        }

        @Override
        public void setActive(boolean active) {
            this.active = active;
        }

        @Override
        public String name() {
            return "Show Path Only";
        }

        @Override
        public boolean countChild(GUIProofTreeNode node, TreeNode parent, int pos) {
            return nodes.contains(node.getNode());
        }

        @Override
        protected boolean countChild(TreeNode child, TreeNode parent, int pos) {
        if (child instanceof GUIProofTreeNode) {
            return nodes.contains(((GUIProofTreeNode)child).getNode());
           // return countChild((GUIProofTreeNode)child, parent, pos);
        } else if (child instanceof GUIBranchNode) {
            Enumeration<TreeNode> tnEnum = child.children();
            boolean hasActiveChildren = false;
            while(tnEnum.hasMoreElements()) {
                TreeNode tn = tnEnum.nextElement();
                hasActiveChildren = countChild(tn, child, -1);
                if (hasActiveChildren) break;
            }
            return hasActiveChildren;
        }
        return true;
        }
}
