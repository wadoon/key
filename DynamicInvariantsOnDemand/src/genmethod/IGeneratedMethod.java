//Code from https://www.javaworld.com/article/2071777/design-patterns/add-dynamic-java-code-to-your-application.html
package genmethod;

import java.util.ArrayList;

public interface IGeneratedMethod {
	
	// Pass a list of input Variables to make the method generic
	GeneratedMethodReturnObject callGeneratedMethod(ArrayList<Integer> inputVariables);
}
