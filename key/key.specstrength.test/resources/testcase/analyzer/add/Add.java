public class Add {
    
   // 6 facts in total, uncovered Facts:
   //
   // Loop body fact, Path condition "y < 0 & !y = i_0"
   // res = -1 + res_0
   // Loop body fact, Path condition "y > -1 & y > i_0"
   // res = 1 + res_0
   /*@ normal_behaviour
     @   ensures \result == x + y;
     @*/
   public /*@pure@*/ int addStrongest(int x, int y) {
       int res = x;
       
       if(y < 0) {
           //@ ghost int oldRes = res + 1;
           /*@ loop_invariant y <= i && i <= 0 && res == x + i && res == oldRes - 1; 
             @ assignable \nothing;
             @ decreases i - y;
             @*/
           for(int i = 0; i > y; i--) {
               //@ set oldRes = res;
               res--;
           }
       } else {
           //@ ghost int oldRes = res - 1;
           /*@ loop_invariant 0 <= i && i <= y && res == x + i && res == oldRes + 1; 
             @ assignable \nothing;
             @ decreases y - i;
             @*/
           for(int i = 0; i < y; i++) {
               //@ set oldRes = res;
               res++;
           }
       }
       
       return res;
   }
     
    // 6 facts in total, uncovered Facts:
    //
    // Loop body fact, Path condition "y < 0 & !y = i_0"
    // res = -1 + res_0
    // Loop body fact, Path condition "y > -1 & y > i_0"
    // res = 1 + res_0
    /*@ normal_behaviour
      @   ensures \result == x + y;
      @*/
    public /*@pure@*/ int addStandard(int x, int y) {
        int res = x;
        
        if(y < 0) {
            /*@ loop_invariant y <= i && i <= 0 && res == x + i; 
              @ assignable \nothing;
              @ decreases i - y;
              @*/
            for(int i = 0; i > y; i--) {
                res--;
            }
        } else {
            /*@ loop_invariant 0 <= i && i <= y && res == x + i; 
              @ assignable \nothing;
              @ decreases y - i;
              @*/
            for(int i = 0; i < y; i++) {
                res++;
            }
        }
        
        return res;
    }
    
   /*@ normal_behaviour
     @   ensures \result == x + y;
     @*/
   public /*@pure@*/ int addTrivialInvariants(int x, int y) {
       int res = x;
       
       if(y < 0) {
           /*@ loop_invariant true; 
             @ assignable \nothing;
             @ decreases i - y;
             @*/
           for(int i = 0; i > y; i--) {
               res--;
           }
       } else {
           /*@ loop_invariant true; 
             @ assignable \nothing;
             @ decreases y - i;
             @*/
           for(int i = 0; i < y; i++) {
               res++;
           }
       }
       
       return res;
   }
}
