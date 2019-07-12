public class CohenCu {
    /*@
      @ public normal_behavior
      @ requires (a >= 1);
      @ ensures \result == (a + 1)*(a + 1)*(a + 1);
      @ diverges true;
      @*/
    int cohencu(int a){
        /* printing consecutive cube, by Cohen */

        int n,x,y,z;
        n=0; x=0; y=1; z=6;
        
        /*@
		  @ loop_invariant z == (6*n + 6) && y == (3*n*n + 3*n + 1) && x == (n*n*n) && n <= (a + 1);
		  @ assignable \nothing;
		  @*/
        while(n <= a){
            //z == 6*n + 6);
            //y == 3*n*n + 3*n + 1);
            //x == n*n*n);
            n=n+1;
            x=x+y;
            y=y+z;
            z=z+6;
        }
        return x;
    }
}
