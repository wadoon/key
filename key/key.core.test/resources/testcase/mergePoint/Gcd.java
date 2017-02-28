// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


public class Gcd {
    
    // Statistics
    // ==========
    // Normal:    9,056
    // ITE:       8,758
    // PredAbstr: 7,591
    
    /*@ public normal_behavior
     @   ensures (a != 0 || b != 0) ==>
     @           (a % \result == 0 && b % \result == 0 &&
     @            (\forall int x; x > 0 && a % x == 0 && b % x == 0;
     @                            \result % x == 0));
     @*/
    public static int gcdMergeContractITE(int a, int b) {
        
        /*@ merge_proc "JoinByIfThenElse";
         @*/
        {
        if (a < 0) a = -a;
        }
        
        /*@ merge_proc "JoinByIfThenElse";
         @*/
        {
        if (b < 0) b = -b;
        }
        
        int big, small;
        
        if (a > b) {
            big = a;
            small = b;
        } else {
            big = b;
            small = a;
        }
        
        return gcdHelp(big, small);
    }
    
    /*@ public normal_behavior
     @   ensures (a != 0 || b != 0) ==>
     @           (a % \result == 0 && b % \result == 0 &&
     @            (\forall int x; x > 0 && a % x == 0 && b % x == 0;
     @                            \result % x == 0));
     @*/
    public static int gcdPredAbstr(int a, int b) {
        
        /*@ merge_proc "JoinByPredicateAbstraction";
         @ merge_params conjunctive(int i -> {i >= 0, i = a | i = -a});
         @*/
        {
            if (a < 0) a = -a;
        }
        
        /*@ merge_proc "JoinByPredicateAbstraction";
         @ merge_params conjunctive(int i2 -> {i2 >= 0, i2 = b | i2 = -b});
         @*/
        {
            if (b < 0) b = -b;
        }
        
        int big, small;
        
        
        if (a > b) {
            big = a;
            small = b;
        } else {
            big = b;
            small = a;
        }
        
        
        return gcdHelp(big, small);
    }

   
       /*@ public normal_behavior
     @   ensures (a != 0 || b != 0) ==>
     @           (a % \result == 0 && b % \result == 0 &&
     @            (\forall int x; x > 0 && a % x == 0 && b % x == 0;
     @                            \result % x == 0));
     @*/
    public static int gcd(int a, int b) {
        
        
        if (a < 0) a = -a;
        
        if (b < 0) b = -b;
        
        int big, small;
        
        
        if (a > b) {
            big = a;
            small = b;
        } else {
            big = b;
            small = a;
        }
        
        return gcdHelp(big, small);
    }
    
    /*@ public normal_behavior
     @   ensures (a != 0 || b != 0) ==>
     @           (a % \result == 0 && b % \result == 0 &&
     @            (\forall int x; x > 0 && a % x == 0 && b % x == 0;
     @                            \result % x == 0));
     @*/
    public static int gcdBlockContract(int a, int b) {
        
        /*@ normal_behavior
         @ ensures a >= 0 && (a == \old(a) || a == - \old(a));
         @*/
        {
        if (a < 0) a = -a;
             }
        
        /*@ normal_behavior
         @ ensures b >= 0 && (b == \old(b) || b == - \old(b));
         @*/
        {
        if (b < 0) b = -b;
        }
        
        int big, small;
        
        
        if (a > b) {
            big = a;
            small = b;
        } else {
            big = b;
            small = a;
        }
        
        return gcdHelp(big, small);
    }

    
    /*@
     @ public normal_behavior
     @   requires _small >= 0 && _big >= _small;
     @   ensures _big != 0 ==>
     @           (_big % \result == 0 && _small % \result == 0 &&
     @            (\forall int x; x > 0 && _big % x == 0 && _small % x == 0;
     @                            \result % x == 0));
     @ assignable \nothing;
     @*/
    private static int gcdHelp(int _big, int _small) {
        int big = _big;
        int small = _small;
        
        /*@
         @ loop_invariant small >= 0 && big >= small &&
         @   (big == 0 ==> _big == 0) &&
         @   (\forall int x; x > 0; (_big % x == 0 && _small % x == 0)
         @                          <==>
         @                          (big % x == 0 && small % x == 0));
         @ decreases small;
         @ assignable \nothing;
         @*/
        while (small != 0) {
            final int t = big % small;
            big = small;
            small = t;
        }
        
        return big;
    }


}
