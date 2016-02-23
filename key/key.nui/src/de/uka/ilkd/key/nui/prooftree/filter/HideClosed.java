package de.uka.ilkd.key.nui.prooftree.filter;

import java.util.function.Predicate;
import de.uka.ilkd.key.nui.prooftree.NUINode;

public class HideClosed implements Predicate<NUINode> {
    @Override
    public boolean test(NUINode node) {
        return !node.isClosed();
    }
}
