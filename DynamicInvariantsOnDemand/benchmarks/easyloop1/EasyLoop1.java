//requires (x >= 0);
//loop_invariant (((x^2 - x*y - z) == 0) && (y >= 0));
//loop_invariant (((x*x - x*y - z) == 0) && (y >= 0));
//loop_invariant ((z == (x - y) * x) && (y >= 0));
public class EasyLoop1 {
  /*@ public normal_behavior 
    @ requires (x >= 0);
    @ ensures \result == x * x;
    @ diverges true;
    @*/   
    public int method1(int x) {
	    int  y = x;
    	int  z = 0;
	
      /*@ loop_invariant (y >= 0);
        @ decreasing y;
        @ assignable z,y;
        @*/
    	while (y > 0) {
	      z = z + x;
	      y = y - 1;
    	}
     	return z;
    }
}