package com.csvanefalk.keytestgen.targetmodels.own;

public class QuantifiedClass {

    public int limit;
    private /*@ spec_public @*/ int arr[];
    private /*@ spec_public @*/ int size;


    // bogus spec to test quantifiers  
    /*@ public normal_behavior
      @ requires (\forall int i; 0 <= i && i < size; arr[i] > 10);
      @ ensures true;
      @*/
    public boolean arrAddandComp(int index1, int index2) {
        if (arr[index1] > arr[10]) {
            return arr[index1] + arr[index2] > 20;
        } else {
            return arr[index1] - arr[index2] < 20;
        }
    }

    /*@ public normal_behavior
      @ ensures \result == (\exists int i; 
      @                                  0 <= i && i < size;
      @                                  arr[i] == elem);
      @*/
    public /* @ pure @ */boolean contains(int elem) {
         /*
         for (int i = 0; i < limit; i++) {
             if (arr[i] == elem) {
                 return true;
             }
         }*/
        return false;
    }
}
