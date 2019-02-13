package profiling.nodecount;

import profiling.ProfilingData;

public class NodeCountData extends ProfilingData {

	private int numberOfNodes;
	
	public NodeCountData(int numberOfNodes) {
		this.numberOfNodes = numberOfNodes;
	}
	
	@Override
	public String toString() {
		return "Number Of Nodes: " + numberOfNodes;
	}
	
}
