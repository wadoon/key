import java.io.FileNotFoundException;

import de.uka.ilkd.key.proof.Proof;
import io.ProofLoader;
import profiling.Profiler;
import profiling.ProfilingData;
import profiling.nodecount.NodeCountProfiler;

public class Main {

	final static String PATH = "proofFiles/identity/identity.proof";
	
	public static void main(String[] args) {
        System.out.println("Welcome to the ProofProfiler!");
        try {
        	if( 0 < args.length ) {
        		if( args[0].equals("simple") ) {
        			ProofLoader proofLoader = new ProofLoader(PATH);
        			Proof proof = proofLoader.getProof();
					Profiler profiler = new NodeCountProfiler();
					ProfilingData data = profiler.profile(proof);
					data.writeToDisk("identity");
            	}
        	}
        } catch (FileNotFoundException e) {
			e.printStackTrace();
		}
    }
}