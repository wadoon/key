class TimesTwo {
	
	/*@
      	  @ public normal_behavior
    	  @ requires 0 <= n;
    	  @ ensures \result == 2*n;
    	  @ diverges true;
    	  @*/
	int timesTwo(int n) {
		int r = 0;
		int i = 0;
		/*@ loop_invariant i<=n && r==i; @*/
		while(i < n) {
			r = r + 1;
			i = i + 1;
		}
		int j = 0;
		/*@ loop_invariant j<=n && r==n+j; @*/
		while(j < n) {
			r = r + 1;
			j = j + 1;
		}
		return r;
	}

}











