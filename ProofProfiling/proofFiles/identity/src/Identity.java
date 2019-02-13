public class Identity {
	
	/*@
      	  @ public normal_behavior
    	  @ requires 0 <= n;
    	  @ ensures \result == n;
    	  @ diverges true;
    	  @*/
	int identity(int n) {
		int i = 0;
		/*@
		  @ loop_invariant (0<=i && i<=n);
		  @ assignable \nothing;
		  @*/
		while(i < n) {
			i = i + 1;
		}
		return i;
	}

}











