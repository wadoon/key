class Square {
	
	/*@
      	  @ public normal_behavior
    	  @ requires 0 <= n;
    	  @ ensures \result == n*n;
    	  @ diverges true;
    	  @*/
	int square(int n) {
		int r = 0;
		int i = 0;
		/*@ loop_invariant i<=n && r==i*n; @*/
		while(i < n) {
			int j = 0;
			/*@ loop_invariant j<=n && r==i*n+j; @*/
			while(j < n) {
				r = r + 1;
				j = j + 1;
			}
			i = i + 1;
		}
		return r;
	}

}











