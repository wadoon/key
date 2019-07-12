public class Pow2 {
  /*@ public normal_behavior 
    @ requires (x >= 0);
    @ ensures \result == x * x;
    @ diverges true;
    @*/   
    public int pow2(int x) {
	    int  y = x;
    	int  z = 0;
    	
	/*@
	  @ loop_invariant ((z == (x - y) * x) && (y >= 0));
	  @ assignable \nothing;
	  @*/
    	while (y > 0) {
	      z = z + x;
	      y = y - 1;
    	}
     	return z;
    }
}
