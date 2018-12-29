package sample;

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

		return traceMethodReturnObject;
	}
}
