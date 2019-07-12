//Code from https://www.javaworld.com/article/2071777/design-patterns/add-dynamic-java-code-to-your-application.html
package gentest;

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import dynacode.DynaCode;
import helperfunctions.HelperFunctions;

public class CallGenTestManuallyAndSaveTraces {

	public static void main(String[] args) throws Exception {
		IGenTest generatedTest = getGeneratedTest();

		HashMap<String, ArrayList<Integer>> varTraces = generatedTest.callGenTest();
		System.out.println("gentest");
		
		//--- Format Traces to DIG Format ---
		int numTraces = 0;
		if (varTraces.values().iterator().hasNext())
			numTraces = varTraces.values().iterator().next().size();
		System.out.println("Write " + numTraces + " traces in DIG format to file..");
		String tracesDIG = HelperFunctions.formatTracesToDIG(varTraces);
		
		
		//--- Write Traces to file in workspace ---
		Path currentPath = Paths.get(System.getProperty("user.dir"));
		Path tracesFilePath = Paths.get(currentPath.toString(), "traces.tcs");
		HelperFunctions.writeStringToFile(tracesDIG, tracesFilePath.toString());
	}

	private static IGenTest getGeneratedTest() {
		DynaCode dynacode = new DynaCode();
		dynacode.addSourceDir(new File("dynacode"));
		return (IGenTest) dynacode.newProxyInstance(IGenTest.class,
				"gentest.GenTest");
	}

}

