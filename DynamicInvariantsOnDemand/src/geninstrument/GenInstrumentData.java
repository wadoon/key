package geninstrument;

import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;

//Singleton class, data storage for information about the generated method
public class GenInstrumentData {
	private static GenInstrumentData instance;

	private GenInstrumentData() {
	}

	public static GenInstrumentData getInstance() {
		if (GenInstrumentData.instance == null) {
			GenInstrumentData.instance = new GenInstrumentData();
		}
		return GenInstrumentData.instance;
	}
	
	// isInitialized = true -> class is useable
	public boolean isInitialized = false;
	
	public LinkedHashSet<String> inputVars;
	public LinkedHashSet<String> allVars;
	public LinkedHashSet<String> nonInputVars;
	public List<String> javaAssignments;
}