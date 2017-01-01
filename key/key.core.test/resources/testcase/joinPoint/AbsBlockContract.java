public class AbsBlockContract {
  
    /*@ public normal_behavior
     @ ensures \result >= 0;
     @*/
    public int absBlockContract(int num) {
        int y;
        
        /*@  join_proc "JoinByIfThenElse";
         @*/
        
        {if (num < 0) {
            y = -num;
        } else {
            y = num;
        }
        }
        int x = 0;
        return y;
    
    }
    
}
