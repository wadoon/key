package profiling;

import de.uka.ilkd.key.proof.Proof;

public interface Profiler {

	public ProfilingData profile(Proof proof);
	
}
