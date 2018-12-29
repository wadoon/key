import TraceMethodReturnObject;

public class EasyLoop1 {
    public TraceMethodReturnObject method1(int x) {
    	TraceMethodReturnObject traceMethodReturnObject = new TraceMethodReturnObject();
	    int  y = x;
    	int  z = 0;
    	//@ loop_invariant ((z == (x - y) * x) && (y >= 0));
    	// -> muss immer am Schleifenanfang und am Ende gelten, ergo:
    	//    es reicht, direkt nach dem Schleifenkopf zu tracen und 1x nach der Schleife
    	//    (da ich ja implizit von der Vorrunde wieder die Endbedingung am Anfang checke)
    	while (y > 0) {
    	  
    	  // Für jede Variable eine beginLoop ArrayList (auch für input Variablen, die könnten sich ja auch verändern)
    	  ArrayList<Integer> beginLoop_x = new ArrayList<Integer>();
    	  ArrayList<Integer> beginLoop_y = new ArrayList<Integer>();
    	  ArrayList<Integer> beginLoop_z = new ArrayList<Integer>();
	      z = z + x;
	      y = y - 1;
    	}
	    ArrayList<Integer> afterLoop_x = new ArrayList<Integer>();
	  	ArrayList<Integer> afterLoop_y = new ArrayList<Integer>();
	  	ArrayList<Integer> afterLoop_z = new ArrayList<Integer>();
	  	
	  	// Fill the return Object
	  	traceMethodReturnObject.beginLoopTraces.add(beginLoop_x);
	  	traceMethodReturnObject.beginLoopTraces.add(beginLoop_y);
	  	traceMethodReturnObject.beginLoopTraces.add(beginLoop_z);
	  	
	  	traceMethodReturnObject.afterLoopTraces.add(afterLoop_x);
	  	traceMethodReturnObject.afterLoopTraces.add(afterLoop_y);
	  	traceMethodReturnObject.afterLoopTraces.add(afterLoop_z);
	  	
	  	traceMethodReturnObject.originalReturnValue = z;
	  	
     	return traceMethodReturnObject;
    }
}