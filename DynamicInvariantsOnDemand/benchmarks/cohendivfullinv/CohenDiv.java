public class CohenDiv {
	
	/*@
    @ public normal_behavior
    @ requires (0 <= x) && (0 < y);
    @ ensures \result*y <= x && x <= (\result+1)*y;
    @ diverges true;
    @*/
	int cohenDiv(int x, int y) {
		int q = 0;	// quotient
		int r = x;	// remainder	
		
		/*@
		  @ loop_invariant (r >= 0) && (x == q*y + r);
		  @ assignable \nothing;
		  @*/
		while(y <= r) {
			int a = 1;
			int b = y;
			/*@
			  @ loop_invariant (b <= r) && (b == a*y);
			  @ assignable \nothing;
			  @*/
			while(2*b <= r) {
				a = 2*a;
				b = 2*b;
			}
			r = r - b;
			q = q + a;
		}
		return q;
	}
}
