class SquareNoPol {
	
	/*@
      	  @ public normal_behavior
    	  @ requires 0 <= n;
    	  @ ensures \result == n*n;
    	  @ diverges true;
    	  @*/
	int square(int n) {
		int r = 0;
		int i = 0;
		// && r==i*n
		/*@ loop_invariant i<=n; @*/
		while(i < n) {
			int j = 0;
			// && r==i*n+j
			/*@ loop_invariant j<=n; @*/
			while(j < n) {
				r = r + 1;
				j = j + 1;
			}
			i = i + 1;
		}
		return r;
	}

}