//FIXME parallel-upd(parallel-upd(elem-update(exc)(null),elem-update(y)(int::select(heap,self,Loop1::$x))),elem-update(z)(Z(0(#))))
//howto deal with heap Variables
public class Loop1 {
  /*@ public invariant x>=0; @*/ 
  public int x;

    
  /*@ public normal_behavior 
    @ ensures \result == x * x;
    @*/   
    public int method1() {
	    int  y = x;
    	int  z = 0;
	
      /*@ loop_invariant ((z == (x - y) * x) && (y >= 0));
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