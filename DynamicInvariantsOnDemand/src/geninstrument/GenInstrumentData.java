package geninstrument;

import java.util.LinkedHashSet;

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
}