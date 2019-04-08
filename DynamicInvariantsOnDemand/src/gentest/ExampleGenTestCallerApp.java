//Code from https://www.javaworld.com/article/2071777/design-patterns/add-dynamic-java-code-to-your-application.html
package gentest;

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import dynacode.DynaCode;

public class ExampleGenTestCallerApp {

	public static void main(String[] args) throws Exception {
		IGenTest generatedTest = getGeneratedTest();

		HashMap<String, ArrayList<Integer>> varTraces = generatedTest.callGenTest();
		System.out.println("gentest");
	}

	private static IGenTest getGeneratedTest() {
		DynaCode dynacode = new DynaCode();
		dynacode.addSourceDir(new File("dynacode"));
		return (IGenTest) dynacode.newProxyInstance(IGenTest.class,
				"gentest.GenTest");
	}

}

