//Code from https://www.javaworld.com/article/2071777/design-patterns/add-dynamic-java-code-to-your-application.html
package sample;

import java.util.ArrayList;

import core.TraceMethodReturnObject;

public interface IGeneratedMethod {
	
	// Pass a list of input Variables to make the method generic
	TraceMethodReturnObject callGeneratedMethod(ArrayList<Integer> inputVariables);
}
