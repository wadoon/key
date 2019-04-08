//Code from https://www.javaworld.com/article/2071777/design-patterns/add-dynamic-java-code-to-your-application.html
package geninstrument;

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import dynacode.DynaCode;

public class ExampleInstrumentCallerApp {

	public static void main(String[] args) throws Exception {
		IGenInstrument generatedMethod = getGeneratedMethod();

		ArrayList<Integer> inputVars = new ArrayList<Integer>();
		inputVars.add(5);

		HashMap<String, ArrayList<Integer>> varLoopHeadTraces = generatedMethod.callGenInstrument(inputVars);
		System.out.println("o");
	}

	private static IGenInstrument getGeneratedMethod() {
		DynaCode dynacode = new DynaCode();
		dynacode.addSourceDir(new File("dynacode"));
		return (IGenInstrument) dynacode.newProxyInstance(IGenInstrument.class,
				"genmethod.GeneratedMethod");
	}

}
