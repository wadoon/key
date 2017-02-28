public class Math {
    
    // PredAbstr: 132
    /*@ public normal_behavior
     @ ensures \result >= 0;
     @*/
    public int absContract(int num) {
        int y;
        /*@  merge_proc "JoinByIfThenElse";
         @*/
        {
            if (num < 0) {
                y = -num;
            }
            else {
                y = num;
            }
        }
        return y;
    }
    
    /*@ public normal_behavior
    @ ensures \result >= 0;
    @*/
    public int absContractPredAbstr(int num) {
        int y;
        /*@ merge_proc "JoinByPredicateAbstraction";
         @ merge_params conjunctive(int x -> {x >= 0});
         @*/
        {
            if (num < 0) {
                y = -num;
            }
            else {
                y = num;
            }
        }
        return y;
    }
    
    /*@ public normal_behavior
     @ ensures \result >= 0;
     @*/
    public int abs(int num) {
        int y;
        if (num < 0) {
            y = -num;
        }
        else {
            y = num;
        }
        return y;
    }

    /*@ public normal_behavior
     @ requires x >= 0 && y >= 0;
     @ ensures \result >= 0;
     @*/
    public int dist(int x, int y) {
        if (y < x) {
            int tmp = x;
            x = y;
            y = tmp;
        }        // join point with (conjunctive) predicate lattice: _ph >= 0, _ph <= _y
        return y - x;
    }
    
    
    /*@ public normal_behavior
     @ requires x >= 0 && y >= 0;
     @ ensures \result >= 0;
     @*/
    public int distMergeContract(int x, int y) {
        /*@ merge_proc "JoinByPredicateAbstraction";
         @ merge_params conjunctive(int ph -> {ph >= 0, ph <= _y});
         @*/
        {
            if (y < x) {
                int tmp = x;
                x = y;
                y = tmp;
            }
        }
        return y - x;
    }
    
    /*@ public normal_behavior
     @ requires x >= 0 && y >= 0;
     @ ensures \result >= 0;
     @*/
    public int distMergeContractITE(int x, int y) {
        /*@ merge_proc "JoinByIfThenElse";
         @*/
        {
            if (y < x) {
                int tmp = x;
                x = y;
                y = tmp;
            }
        }
        return y - x;
    }
    
    /*@ public normal_behavior
     @ requires x >= 0 && y >= 0;
     @ ensures \result >= 0;
     @*/
    public int distMergeContractError(int x, int y) {
        /*@ merge_proc "JoinByIfThenElse";
         @
         @*/
        {
            if (y < x) {
                int tmp = x;
                x = y;
                y = tmp;
            }
        }
        
        return y - x;
    }

    /*@ public normal_behavior
     @ requires x >= 0 && y >= 0;
     @ ensures \result >= 0;
     @*/
    public int distBlockContract(int x, int y) {
        /*@ normal_behavior
         @ ensures x <= y;
         @*/
        {
            if (y < x) {
                int tmp = x;
                x = y;
                y = tmp;
            }
        }
        
        return y - x;
    }

    /*@ public normal_behavior
     @ ensures \result > 0;
     @*/
    public int notNullContract(int num){
        int y;
        
        /*@  merge_proc "JoinByIfThenElse";
         @*/
        {
            if (num < 0) {
                y = -num;
            }
            else if(num == 0) {
                y = 1;
            }
            else{
                y = num;
            }
        }
        return y;
    }
    
    /*@ public normal_behavior
     @ ensures \result >= 0;
     @*/
    public int notNull(int num){
        int y;
        if (num < 0) {
            y = -num;
        }
        else if(num == 0) {
            y = 1;
        }
        else{
            y = num;
        }
        return y;
    }
    
    /*@ public normal_behavior
     @ ensures \result > 0;
     @*/
    public int notNullNested(int num) {
        int y;
        
        /*@  merge_proc "JoinByIfThenElse";
         @*/
        {
            if (num < 0) {
                y = -num;
            }
            else {
                /*@  merge_proc "JoinByIfThenElse";
                 @*/
                {
                    if(num == 0){
                        y=1;
                    }
                    else{
                        y = num;
                    }
                }
            }
        }
        return y;
    }
    
    /*@ public normal_behavior
     @ ensures \result > 0;
     @*/
    public int notNullNested2(int num) {
        int y;
        
        /*@  merge_proc "JoinByIfThenElse";
         @*/
        {
            if (num <= 0) {
                /*@  merge_proc "JoinByIfThenElse";
                 @*/
                {
                    if(num == 0){
                        y=1;
                    }
                    else{
                        y = -num;
                    }
                }
            }
            else {
                y = num;
            }
        }
            
        return y;
    }

    
    /*@ public normal_behavior
     @ ensures divisor != 0 ==> \result == divident / divisor;
     @ ensures divisor == 0 ==> \result == Integer.MAX_VALUE;
     @*/
    public int divContract(int divident, int divisor) {
        int result;
        /*@  merge_proc "JoinByIfThenElse";
         @*/
        {
            try {
                result = divident / divisor;
            } catch (ArithmeticException e) {
                result = Integer.MAX_VALUE;
            }
        }
        return result;
    }
    
    /*@ public normal_behavior
     @ ensures divisor != 0 ==> \result == divident / divisor;
     @ ensures divisor == 0 ==> \result == Integer.MAX_VALUE;
     @*/
    public int div(int divident, int divisor) {
        int result;
        
        try {
            result = divident / divisor;
        } catch (ArithmeticException e) {
            result = Integer.MAX_VALUE;
        }
        
        return result;
    }


}
