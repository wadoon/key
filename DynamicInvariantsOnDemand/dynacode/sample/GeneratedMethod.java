//Code from https://www.javaworld.com/article/2071777/design-patterns/add-dynamic-java-code-to-your-application.html
package sample;

import java.io.*;
import java.util.ArrayList;

import core.TraceMethodReturnObject;

// This is the generated source
public class GeneratedMethod implements IGeneratedMethod {
	public GeneratedMethod() {
	}

	//this implementation is the generated method
	public TraceMethodReturnObject callGeneratedMethod(ArrayList<Integer> inputVariables) {
		TraceMethodReturnObject traceMethodReturnObject = new TraceMethodReturnObject();
		traceMethodReturnObject.afterLoopTraces = inputVariables;
		for (Integer var : inputVariables) {
			System.out.println(var);
		}
		return traceMethodReturnObject;
	}
}
