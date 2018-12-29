package genmethod;
import java.util.ArrayList;

// An object of this class is returned by the generated trace method in Order to pass the original return value (1 Integer) and the traces at each loopBegin and 1 trace after Loop
public class GeneratedMethodReturnObject {
	// Inner ArrayList: n Traces for 1 Variable. Outer ArrayList: Holds m Variable Traces.
	public ArrayList<ArrayList<Integer>> beginLoopTraces = new ArrayList<ArrayList<Integer>>();
	// Technically, I need only need ArrayList<Integer> here, since there is only 1 trace after Loop for each variable.
	public ArrayList<Integer> afterLoopTraces = new ArrayList<Integer>();
	
	public int originalReturnValue;
}
