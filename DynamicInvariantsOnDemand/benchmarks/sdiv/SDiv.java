class SDiv {
   
    /*@ public normal_behaviour 
      @ requires (x > y && x > 0 && y > 0);
      @ ensures ((\result * y) <= x && ((\result+1) * y) >= x);
      @ diverges true;
      @ */
    public int sdiv(int x, int y) {
	    int q = 0;

	    //(q*y + _x == x)
  /*@ loop_invariant ((x >= 0));
    @*/
      while (x >= y) {
    	  x = x - y;
	      q = q + 1;
    	}
    	return q;
    }

    
}