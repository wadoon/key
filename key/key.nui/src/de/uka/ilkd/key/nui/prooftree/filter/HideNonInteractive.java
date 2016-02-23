package de.uka.ilkd.key.nui.prooftree.filter;

import java.util.function.Predicate;

import de.uka.ilkd.key.nui.prooftree.NUIBranchNode;
import de.uka.ilkd.key.nui.prooftree.NUILeafNode;
import de.uka.ilkd.key.nui.prooftree.NUINode;

public class HideNonInteractive implements Predicate<NUINode> {

    @Override
    public boolean test(NUINode node) {
        if (node instanceof NUIBranchNode || node instanceof NUILeafNode) {
            return true;
        }
        else {
            return node.isInteractive();
        }
    }

}