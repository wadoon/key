public class DoubleAbs {
    
    /*@ public normal_behavior
     @  ensures result >= 0;
     @*/ 
    public int doubleAbs(int num) {
        int y = 0, x = 0;
        
        //@ merge_proc "JoinByPredicateAbstraction";
        {
            if (num < 0) {
                y = -num;
            } else {
                y = num;
            }
        }
        
        /*@ merge_proc "JoinByPredicateAbstraction";
         @  merge_params "simple(int x -> {x >= 0})";
         @*/         {
            if (num < 0) {
                x = -num;
            } else {
                x = num;
            }
        }
        
        return x + y;
    }

    //@ public normal_behavior
    //@ ensures result >= 0;
    public int doubleAbsPredAbstr(int num) {
        int y = 0, x = 0;
        
        /*@ merge_proc "JoinByPredicateAbstraction";
         @ merge_params "simple(int x -> {x >= 0})";
         @*/
        {
            if (num < 0) {
                y = -num;
            } else {
                y = num;
            }
        }
        
        /*@ merge_proc "JoinByPredicateAbstraction";
         @ merge_params "simple(int x -> {x >= 0})";
         @*/
        {
            if (num < 0) {
                x = -num;
            } else {
                x = num;
            }
        }
        
        return x + y;
    }
      //@ public normal_behavior
     //@ ensures result >= 0;
    public int doubleAbsNoContract(int num) {
        int y = 0, x = 0;
            if (num < 0) {
                y = -num;
            } else {
                y = num;
            }
      
            if (num < 0) {
                x = -num;
            } else {
                x = num;
            }
        
        return x + y;
    }

}
