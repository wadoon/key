package genmethod;

import java.util.LinkedHashSet;

//Singleton class, data storage for information about the generated method
public class GenMethodData {
	private static GenMethodData instance;

	private GenMethodData() {
	}

	public static GenMethodData getInstance() {
		if (GenMethodData.instance == null) {
			GenMethodData.instance = new GenMethodData();
		}
		return GenMethodData.instance;
	}
	
	// isInitialized = true -> class is useable
	public boolean isInitialized = false;
	
	public LinkedHashSet<String> inputVars;
}