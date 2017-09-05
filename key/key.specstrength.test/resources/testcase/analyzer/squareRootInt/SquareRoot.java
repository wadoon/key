public class SquareRoot {
    
    /*@ model_behavior
      @ ensures \result == n * n;
      @ static model int square(int n);
      @*/
    
    /*@ public normal_behavior
      @ requires n >= 0;
      @ ensures    \result * \result <= n
      @         && n < (\result + 1) * (\result + 1);
      @*/
    public static int sqrt(int n) {
        int r = n;
        int y = r*r;
        int z = -2*r + 1;
        
        /*@ loop_invariant
          @   0 <= r && r <= n &&
          @   y == r*r         &&
          @   z == -2*r + 1    &&
          @   (r+1) * (r+1) > n;
          @ decreases r;
          @*/
        while (y > n) {
            r--;
            
            y += z;
            z += 2;
        }
        
        return r;
    }
    
}
