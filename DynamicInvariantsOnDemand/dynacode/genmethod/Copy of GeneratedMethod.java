//Code from https://www.javaworld.com/article/2071777/design-patterns/add-dynamic-java-code-to-your-application.html
package genmethod;

import java.io.*;
import java.util.ArrayList;

// This is the generated source
public class GeneratedMethod implements IGeneratedMethod {
	//this implementation is the generated method
	public GeneratedMethodReturnObject callGeneratedMethod(ArrayList<Integer> inputVariables) {
		GeneratedMethodReturnObject generatedMethodReturnObject = new GeneratedMethodReturnObject();
		generatedMethodReturnObject.afterLoopTraces = inputVariables;
		for (Integer var : inputVariables) {
			System.out.println(var);
		}
		return generatedMethodReturnObject;
	}
}
