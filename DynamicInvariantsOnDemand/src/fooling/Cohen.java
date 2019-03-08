package fooling;

public class Cohen {
	
	public Cohen() {
		super();
	}
	/*@
    @ public normal_behavior
    @ requires (0 <= x) && (0 < y);
    @ ensures \result*y <= x && x <= (\result+1)*y;
    @ diverges true;
    @*/
	public int cohenDivide(int x, int y) {
		System.out.println("input.x: " + x);
		System.out.println("input.y: " + y);
		int q = 0;	// quotient
		int r = x;	// remainder
		//		  
		/*@
		  @ loop_invariant (0 <= r) && (x == q*y + r);
		  @ assignable \nothing;
		  @*/
		while(y <= r) {
			System.out.println("y <= r <=> " + y + " <= " + r + " -> true");
			int a = 1;
			int b = y;
			System.out.println("outer.a: " + a);
			System.out.println("outer.b: " + b);
			System.out.println("outer.r: " + r);
			System.out.println("outer.q: " + q);
			/*@
			  @ loop_invariant (b <= r) && (b == a*y) && (x == q*y + r);
			  @ assignable \nothing;
			  @*/
			while(2*b <= r) {
				System.out.println("2*b <= r <=> " + 2*b + " <= " + r + " -> true");
				System.out.println("inner.a: " + a);
				System.out.println("inner.b: " + b);
				a = 2*a;
				b = 2*b;
			}
			r = r - b;
			q = q + a;
		}
		return q;
	}
	
}
