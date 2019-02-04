//Code from https://www.javaworld.com/article/2071777/design-patterns/add-dynamic-java-code-to-your-application.html
package genmethod;

import java.util.ArrayList;
import java.util.HashMap;

public interface IGeneratedMethod {
	
	// Pass a list of input Variables to make the method generic
	HashMap<String, ArrayList<Integer>> callGeneratedMethod(ArrayList<Integer> inputVariables);
}
