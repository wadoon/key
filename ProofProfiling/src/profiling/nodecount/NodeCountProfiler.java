package profiling.nodecount;

import java.util.Iterator;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import profiling.Profiler;
import profiling.ProfilingData;

public class NodeCountProfiler implements Profiler {

	@Override
	public ProfilingData profile(Proof proof) {
		Node root = proof.root();
		final Iterator<Node> it = root.subtreeIterator();
		int numberOfNodes = 0;
		Node currentNode;
        while (it.hasNext()) {
        	currentNode = it.next();
        	numberOfNodes++;
        }
        return new NodeCountData(numberOfNodes);
	}

}
