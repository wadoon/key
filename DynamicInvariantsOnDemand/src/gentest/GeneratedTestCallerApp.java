//Code from https://www.javaworld.com/article/2071777/design-patterns/add-dynamic-java-code-to-your-application.html
package gentest;

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import dynacode.DynaCode;

public class GeneratedTestCallerApp {

	public static void main(String[] args) throws Exception {
		IGeneratedTest generatedTest = getGeneratedTest();

		HashMap<String, ArrayList<Integer>> varTraces = generatedTest.callGeneratedTest();
		System.out.println("gentest");
	}

	private static IGeneratedTest getGeneratedTest() {
		DynaCode dynacode = new DynaCode();
		dynacode.addSourceDir(new File("dynacode"));
		return (IGeneratedTest) dynacode.newProxyInstance(IGeneratedTest.class,
				"gentest.GeneratedTest");
	}

}

