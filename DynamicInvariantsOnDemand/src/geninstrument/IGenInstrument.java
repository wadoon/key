//Code from https://www.javaworld.com/article/2071777/design-patterns/add-dynamic-java-code-to-your-application.html
package geninstrument;

import java.util.ArrayList;
import java.util.HashMap;

public interface IGenInstrument {
	
	// Pass a list of input Variables to make the method generic
	HashMap<String, ArrayList<Integer>> callGenInstrument(ArrayList<Integer> inputVariables);
}
