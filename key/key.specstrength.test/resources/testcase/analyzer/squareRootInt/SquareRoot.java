public class SquareRoot {
    
    /*@ public normal_behavior
      @ requires n >= 0;
      @ ensures    \result * \result <= n
      @         && n < (\result + 1) * (\result + 1)
      @         && \result >= 0
      @         // && (\forall int x; x >= 0 && x * x <= n && n < (x+1)*(x+1); \result == x)
      @   ;
      @*/
    public static int sqrt(int n) {
        int r = n;
        int y = r*r;
        int z = -2*r + 1;
        
        //@ ghost int r0 = r + 1;
        //@ ghost int y0 = y + 2*r0 - 1;
        
        /*@ loop_invariant
          @   0 <= r            && 
          @   r <= n            &&
          @   y == r*r          &&
          @   z == -2*r + 1     &&
          @   (r+1) * (r+1) > n &&
          @   r == r0 - 1       && // those two formulas are not necessary for proving the method,
          @   y == 1 - 2*r0 + y0;  // but for achieving more strength.
          @ decreases r;
          @*/
        while (y > n) {
            //@ set y0 = y;
            //@ set r0 = r;
            r--;
            
            y += z;
            z += 2;
        }
        
        /* // Lemma needed for post cond:
         * // Existence and uniqueness of Integer square root
         * \forall int n;
         *   (   n >= 0
         *    -> \exists int r;
         *         (  r >= 0
         *          & r * r <= n
         *          & n < (r + 1) * (r + 1)
         *          & !\exists int o; (!o = r & o >= 0 & o * o <= n & n < (o + 1) * (o + 1))))
         */
        // Still, manual interaction needed for using lemma sensibly.
        
        return r;
    }
    
    /*@ requires n >= 0;
      @ requires r*r <= n && n < (r+1)*(r+1);
      @ ensures \result*\result <= n+1 && n+1 < (\result+1)*(\result+1);
      @ ensures \result == r || \result == r+1;
      @*/
    public static int nextSqrt(final int n, final int r) {
        final int p = (n+1) - r*r;
        if (p > r+r) {
            return r+1;
        } else {
            return r;
        }
    }
    
    /*@ requires n >= 0;
      @ ensures    \result * \result <= n
      @         && n < (\result + 1) * (\result + 1)
      @   ;
      @*/
    public static int sqrtIt(int n) {
        int sqrt = 0;
        
        /*@ loop_invariant
          @      i >= 0 && i <= n
          @   && sqrt * sqrt <= i
          @   && i < (sqrt + 1) * (sqrt + 1);
          @ decreases n - i;
          @*/
        for (int i = 0; i < n; i++) {
            sqrt = nextSqrt(i, sqrt);
        }
        
        return sqrt;
    }
    
}
