package profiling.statistics;

import de.uka.ilkd.key.proof.Statistics;
import profiling.ProfilingData;

public class StatiticsData extends ProfilingData {

	private Statistics statistics;
	
	public StatiticsData(Statistics numberOfNodes) {
		this.statistics = numberOfNodes;
	}
	
	@Override
	public String toString() {
		return statistics.toString() ;
	}
}
