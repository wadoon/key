package profiling;

import java.io.FileNotFoundException;
import java.io.PrintWriter;

public class ProfilingData {

	public final String fileEnding = ".profile";
	
	public void writeToDisk(String fileName) throws FileNotFoundException {
		PrintWriter printWriter = new PrintWriter(fileName + fileEnding);
		printWriter.println(toString());
		printWriter.close();
	}
	
}
