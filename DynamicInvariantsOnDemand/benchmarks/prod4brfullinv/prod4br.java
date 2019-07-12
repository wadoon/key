public class Prod4Br {
    /*@
      @ public normal_behavior
      @ requires (x >= 0) && (y >= 0);
      @ ensures \result == x * y;
      @ diverges true;
      @*/
    int prod4br(int x, int y){
  /* algorithm for computing the product of two natural numbers */

	int a,b,p,q;

	a = x;
	b = y;
	p = 1;
	q = 0;
	/*@ loop_invariant (a >= 0) && (b >= 0) &&  q+a*b*p==x*y; @ */
	while(a > 0 && b > 0){ 
		//q+a*b*p==x*y

		if (a % 2 ==0 && b % 2 ==0 ){
			a =a/2;
			b = b/2;
			p = 4*p;
		}
		else if (a % 2 ==1 && b % 2 ==0 ){
			a =a-1;
			q = q+b*p;
		}
		else if (a % 2 ==0 && b % 2 ==1 ){
			b =b-1;
			q = q+a*p;
		}
		else {
			a =a-1;
			b =b-1;
			q = q+(a+b+1) * p;
		}
	}

	//q == x*y
	return q; 

	}
}