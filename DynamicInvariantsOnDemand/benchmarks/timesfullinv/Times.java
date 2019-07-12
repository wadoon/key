class Times {
	
	/*@
  	  @ public normal_behavior
	  @ requires 0 <= a && 0 <= b;
	  @ ensures \result == a*b;
	  @ diverges true;
	  @*/
	int times(int a, int b) {
		int r = 0;
		int i = 0;
		/*@ loop_invariant i<=a && r==i*b; @*/
		while(i < a) {
			int j = 0;
			/*@ loop_invariant j<=b && r==i*b+j; @*/
			while(j < b) {
				r = r + 1;
				j = j + 1;
			}
			i = i + 1;
		}
		return r;
	}

}