//Code from https://www.javaworld.com/article/2071777/design-patterns/add-dynamic-java-code-to-your-application.html
package sample;

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import core.TraceMethodReturnObject;
import dynacode.DynaCode;

public class GeneratedMethodCallerApp {

	public static void main(String[] args) throws Exception {
		IGeneratedMethod generatedMethod = getGeneratedMethod();

		ArrayList<Integer> inputVars = new ArrayList<Integer>();
		inputVars.add(5);
		inputVars.add(3);

		TraceMethodReturnObject o = generatedMethod.callGeneratedMethod(inputVars);
		System.out.println("o");
	}

	private static IGeneratedMethod getGeneratedMethod() {
		DynaCode dynacode = new DynaCode();
		dynacode.addSourceDir(new File("dynacode"));
		return (IGeneratedMethod) dynacode.newProxyInstance(IGeneratedMethod.class,
				"sample.GeneratedMethod");
	}

}
