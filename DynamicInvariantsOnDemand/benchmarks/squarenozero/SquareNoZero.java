class SquareNoZero {
	
	/*@
      	  @ public normal_behavior
    	  @ requires 0 <= n;
    	  @ ensures \result == n*n;
    	  @ diverges true;
    	  @*/
	int square(int n) {
		int r = 0;
		int i = 1;
		/*@ loop_invariant (i-1)<=n && r==(i-1)*n; @*/
		while((i-1) < n) {
			int j = 1;
			/*@ loop_invariant (j-1)<=n && r==(i-1)*n+(j-1); @*/
			while((j-1) < n) {
				r = r + 1;
				j = j + 1;
			}
			i = i + 1;
		}
		return r;
	}

}














