package com.csvanefalk.keytestgen.targetmodels.own;

public class LimitedIntegerSet {
    public final int limit;
    private /*@ spec_public @*/ int arr[];
    private /*@ spec_public @*/ int size = 0;

    public LimitedIntegerSet(int limit) {
        this.limit = limit;
        this.arr = new int[limit];
    }


    /*@ public normal_behavior
      @ ensures !contains(elem);
      @ ensures (\forall int e;
      @                   e != elem;
      @                      contains(e) <==> \old(contains(e)));
      @ ensures \old(contains(elem))
      @               ==> size == \old(size) - 1;
      @ ensures !\old(contains(elem))
      @               ==> size == \old(size);
      @*/
    public void remove(int elem) {

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

    /*@ public normal_behavior
    @ requires size < limit && !contains(elem);
    @ ensures \result == true;
    @ ensures contains(elem);
    @ ensures (\forall int e;
    @                   e != elem;
    @                   contains(e) <==> \old(contains(e)));
    @
    @ ensures size == \old(size) + 1;
    @
    @ also
    @
    @ public normal_behavior
    @ requires (size == limit) || contains(elem);
    @ ensures \result == false;
    @ ensures (\forall int e;
    @                   contains(e) <==> \old(contains(e)));
    @ ensures size == \old(size);
    @*/
    public boolean add(int elem) {
        if (size == limit) {
            return false;
        } else {
            arr[size++] = elem;
            return true;
        }
    }
}
