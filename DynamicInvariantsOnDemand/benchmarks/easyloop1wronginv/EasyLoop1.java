public class EasyLoop1 {
  /*@ public normal_behavior 
    @ requires (x >= 0);
    @ ensures \result == x * x;
    @ diverges true;
    @*/   
    public int square(int x) {
	    int  y = x;
    	int  z = 0;
//loop_invariant (((x*x - x*y - z) == 0) && (y >= 0));
	//@ loop_invariant (((x - x*y - z) == 0) && (y >= 0));
    	while (y > 0) {
	      z = z + x;
	      y = y - 1;
    	}
     	return z;
    }
}
