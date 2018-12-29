package core;
//FIXME 1
import genmethod.GeneratedMethodReturnObject;

import java.util.ArrayList;
//import groovy.util.Eval


public class MainMuster_EasyLoop1 {
	public static void main(String[] args) {
		//Caller
		GeneratedMethodReturnObject traceMethodReturnObject = method1(5);
		System.out.println("done");
	}
	
    public static GeneratedMethodReturnObject method1(int x) {
    	//Callable
    	GeneratedMethodReturnObject traceMethodReturnObject = new GeneratedMethodReturnObject();
	    int  y = x;
    	int  z = 0;
    	//@ loop_invariant ((z == (x - y) * x) && (y >= 0));
    	// -> muss immer am Schleifenanfang und am Ende gelten, ergo:
    	//    es reicht, direkt nach dem Schleifenkopf zu tracen und 1x nach der Schleife
    	//    (da ich ja implizit von der Vorrunde wieder die Endbedingung am Anfang checke)
    	
    	//FIXME 2
	  	// Für jede Variable eine beginLoop ArrayList (auch für input Variablen, die könnten sich ja auch verändern)
	  	ArrayList<Integer> beginLoop_x = new ArrayList<Integer>();
	  	ArrayList<Integer> beginLoop_y = new ArrayList<Integer>();
	  	ArrayList<Integer> beginLoop_z = new ArrayList<Integer>();
	  	
    	while (y > 0) {
    		//FIXME 3
			// Assign to traces at head
			beginLoop_x.add(x);
			beginLoop_y.add(y);
			beginLoop_z.add(z);
				
			z = z + x;
			y = y - 1;
    	}
    	//FIXME 4
	    int afterLoop_x = x;
	  	int afterLoop_y = y;
	  	int afterLoop_z = z;
	  	
	  	//FIXME 5
	  	// Fill the return Object
	  	traceMethodReturnObject.beginLoopTraces.add(beginLoop_x);
	  	traceMethodReturnObject.beginLoopTraces.add(beginLoop_y);
	  	traceMethodReturnObject.beginLoopTraces.add(beginLoop_z);
	  	
	  	traceMethodReturnObject.afterLoopTraces.add(afterLoop_x);
	  	traceMethodReturnObject.afterLoopTraces.add(afterLoop_y);
	  	traceMethodReturnObject.afterLoopTraces.add(afterLoop_z);
	  	
	  	traceMethodReturnObject.originalReturnValue = z;
	  	
	  	//FIXME 6
     	return traceMethodReturnObject;
    }
}