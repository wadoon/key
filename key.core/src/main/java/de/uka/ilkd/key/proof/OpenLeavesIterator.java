package de.uka.ilkd.key.proof;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.NoSuchElementException;

public class OpenLeavesIterator implements Iterator<Node> {

    //private final Node root;
    private final LinkedList<Node> toCheck = new LinkedList<>();
    //private boolean checkedNext = false;

    public OpenLeavesIterator(final Node node) {
        //root = node;
        //n = node;
        toCheck.add(node);
    }

    @Override
    public boolean hasNext() {
        if (toCheck.isEmpty()) {
            return false;
        }
        while (!toCheck.isEmpty()) {
            if (toCheck.getFirst().isClosed()) {
                toCheck.removeFirst();
            } else if (toCheck.getFirst().leaf()) {
                return true;
            } else {
                Node f = toCheck.removeFirst();
                final Iterator<Node> it = f.childrenIterator();
                while (it.hasNext()) {
                    toCheck.addFirst(it.next());
                }
            }

        }
        return false;
    }

    @Override
    public Node next() {
        // hasNext() changes n
        if (!hasNext()) {
            throw new NoSuchElementException("Already exhausted iterator");
        }
        return toCheck.removeFirst();
    }
}
