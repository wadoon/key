package genmethod;

import java.util.ArrayList;

public class GeneratedMethod implements IGeneratedMethod {
	
	public GeneratedMethodReturnObject callGeneratedMethod(ArrayList<Integer> inputVariables) {
    	GeneratedMethodReturnObject generatedMethodReturnObject = new GeneratedMethodReturnObject();
    	
    	// Build seperate input var names from inputVariables list
    	int x = inputVariables.get(0);
    	int y = inputVariables.get(1);
    	
    	int q = 0;	// quotient
		int r = x;	// remainder
		
		//before outer loop accessible
    	ArrayList<Integer> beginLoop_x = new ArrayList<Integer>();
	  	ArrayList<Integer> beginLoop_y = new ArrayList<Integer>();
	  	ArrayList<Integer> beginLoop_q = new ArrayList<Integer>();
	  	ArrayList<Integer> beginLoop_r = new ArrayList<Integer>();
	  	
		//only in inner loop accessible (second invGen call)
	  	//especially, we don't want duplicate variables like q_0 and q here
    	ArrayList<Integer> beginLoop_a = new ArrayList<Integer>();
	  	ArrayList<Integer> beginLoop_b = new ArrayList<Integer>();
	  	
		while(y <= r) {
			// Assign to traces at head
			beginLoop_x.add(x);
			beginLoop_y.add(y);
			beginLoop_q.add(q);
			beginLoop_r.add(r);
			
			int a = 1;
			int b = y;

			while(2*b <= r) {
				// Assign to traces at head
				//FIXME: What to to, if x, y, r or r get updated here? then we even need duplicate traces for then for both invariants
				beginLoop_a.add(a);
				beginLoop_b.add(b);
				
				a = 2*a;
				b = 2*b;
			}
			// Even more problems here.. sorting of variables in afterlooptraces
		  	generatedMethodReturnObject.afterLoopTraces.add(a);
		  	generatedMethodReturnObject.afterLoopTraces.add(b);
		  	
			r = r - b;
			q = q + a;
		}
    	// Record last after-Loop traces (invariant true before and after loop)
	    int afterLoop_x = x;
	  	int afterLoop_y = y;
	  	int afterLoop_q = q;
		int afterLoop_r = r;
	  	
	  	// Fill the return Object
	  	generatedMethodReturnObject.beginLoopTraces.add(beginLoop_x);
	  	generatedMethodReturnObject.beginLoopTraces.add(beginLoop_y);
	  	generatedMethodReturnObject.beginLoopTraces.add(beginLoop_q);
	  	generatedMethodReturnObject.beginLoopTraces.add(beginLoop_r);
	  	generatedMethodReturnObject.beginLoopTraces.add(beginLoop_a);
	  	generatedMethodReturnObject.beginLoopTraces.add(beginLoop_b);
	  	
	  	generatedMethodReturnObject.afterLoopTraces.add(afterLoop_x);
	  	generatedMethodReturnObject.afterLoopTraces.add(afterLoop_y);
	  	generatedMethodReturnObject.afterLoopTraces.add(afterLoop_q);
	  	generatedMethodReturnObject.afterLoopTraces.add(afterLoop_r);
	  	
	  	generatedMethodReturnObject.originalReturnValue = q;
	  	
     	return generatedMethodReturnObject;
    }
}

public class SimpleExamples {
	
	/*@
    @ public normal_behavior
    @ requires (0 <= x) && (0 < y);
    @ ensures \result*y <= x && x <= (\result+1)*y;
    @ diverges true;
    @*/
	int cohenDivide(int x, int y) {
		int q = 0;	// quotient
		int r = x;	// remainder
		//		  
		/*@
		  @ loop_invariant (0 <= r) && (x == q*y + r);
		  @ assignable \nothing;
		  @*/
		while(y <= r) {
			int a = 1;
			int b = y;
			/*@
			  @ loop_invariant (b <= r) && (b == a*y) && (x == q*y + r);
			  @ assignable \nothing;
			  @*/
			while(2*b <= r) {
				a = 2*a;
				b = 2*b;
			}
			r = r - b;
			q = q + a;
		}
		return q;
	}
	
}