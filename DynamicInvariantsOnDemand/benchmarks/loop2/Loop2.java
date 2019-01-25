class Loop2 {
   
    //@ public invariant x > y && x > 0 && y > 0;
    public int x;
    public int y;
    
    /*@ public normal_behaviour 
      @ ensures ((\result * y) <= x && ((\result+1) * y) >= x);
      @
      @ */
    public int method2() {
	    int  x1 = x, q = 0;


  /*@ loop_invariant ((x1 >= 0) && (q*y + x1 == x));
    @ decreasing x1;
    @ assignable q, x1;
    @*/
      while (x1 >= y) {
	      x1 = x1 - y;
	      q = q + 1;
    	}
    	return q;
    }

    
}