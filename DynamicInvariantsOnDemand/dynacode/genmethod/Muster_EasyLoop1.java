package genmethod;

import java.util.ArrayList;

public class GeneratedMethod implements IGeneratedMethod {
	
	public GeneratedMethodReturnObject callGeneratedMethod(ArrayList<Integer> inputVariables) {
    	GeneratedMethodReturnObject generatedMethodReturnObject = new GeneratedMethodReturnObject();
    	
    	// Build seperate input var names from inputVariables list
    	int x = inputVariables.get(0);
    	
	    int  y = x;
    	int  z = 0;
    	//@ loop_invariant ((z == (x - y) * x) && (y >= 0));
    	// -> muss immer am Schleifenanfang und am Ende gelten, ergo:
    	//    es reicht, direkt nach dem Schleifenkopf zu tracen und 1x nach der Schleife
    	//    (da ich ja implizit von der Vorrunde wieder die Endbedingung am Anfang checke)
    	
    	ArrayList<Integer> beginLoop_x = new ArrayList<Integer>();
	  	ArrayList<Integer> beginLoop_y = new ArrayList<Integer>();
	  	ArrayList<Integer> beginLoop_z = new ArrayList<Integer>();
    	while (y > 0) {
			// Assign to traces at head
			beginLoop_x.add(x);
			beginLoop_y.add(y);
			beginLoop_z.add(z);
				
			z = z + x;
			y = y - 1;
    	}
    	// Record last after-Loop traces (invariant true before and after loop)
	    int afterLoop_x = x;
	  	int afterLoop_y = y;
	  	int afterLoop_z = z;
	  	
	  	// Fill the return Object
	  	generatedMethodReturnObject.beginLoopTraces.add(beginLoop_x);
	  	generatedMethodReturnObject.beginLoopTraces.add(beginLoop_y);
	  	generatedMethodReturnObject.beginLoopTraces.add(beginLoop_z);
	  	
	  	generatedMethodReturnObject.afterLoopTraces.add(afterLoop_x);
	  	generatedMethodReturnObject.afterLoopTraces.add(afterLoop_y);
	  	generatedMethodReturnObject.afterLoopTraces.add(afterLoop_z);
	  	
	  	generatedMethodReturnObject.originalReturnValue = z;
	  	
     	return generatedMethodReturnObject;
    }
}

