package profiling.statistics;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;
import profiling.Profiler;
import profiling.ProfilingData;

public class StatisticsProfiler implements Profiler {

	@Override
	public ProfilingData profile(Proof proof) {
		Node root = proof.root();
		Statistics stat = new Statistics(root);
		StatiticsData statdata= new StatiticsData(stat);
		// TODO Auto-generated method stub
		return statdata;
	}
	
}