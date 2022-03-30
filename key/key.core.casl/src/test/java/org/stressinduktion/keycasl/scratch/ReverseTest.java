package org.stressinduktion.keycasl.scratch;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Objects;

public class ReverseTest {

    static class Nat {

        public int i;

        public Nat(int i) {
            this.i = i;
        }

        public boolean equals(Nat n) {
            return this.i == n.i;
        }

        // /*@ requires b != null;
        // @ ensures (\forall int x; 0 <= x < b.length; \result[\result.length-x-1] == \old(b[x]));
        // @*/
        // Nat[] reverse_int(Nat[] b) {
        //  Nat[] a_ = new Nat[b.length];
        //  /*@ loop_invariant 0 <= i && i <= b.length;
        //    @ loop_invariant (\forall int x; 0 <= x < i; a_[x] == b[b.length-x-1]);
        //    @ decreases b.length - i;
        //    @ assignable a_[*];
        //    @*/
        //  for (int i = 0; i < b.length; i++) {
        //      a_[i] = b[b.length - i - 1];
        //  }
        //  return a_;
        // }

        // /*@ requires is != null;
        // @ ensures \fresh(\result);
        // @*/
        // int[] cons(int i, int[] is) {
        //  int[] is_ = new int[is.length + 1];
        //  is_[0] = i;
        //  /*@ loop_invariant 1 <= idx <= is_.length;
        //    @ loop_invariant (\forall int x; 1 <= x < idx; is_[idx] == is[idx-1]);
        //    @ decreases is_.length - idx;
        //    @ assignable is_[1 .. is_.length];
        //    @*/
        //  for (int idx = 1; idx < is_.length; idx++) {
        //      is_[idx] = is[idx-1];
        //  }
        //  return is_;
        // }
    }


    interface INatList {
        //@ public instance model \dl_NatList nlist;

        // free data type?
        //@ public instance model \locset footprint;
        //@ public instance accessible \inv : footprint;

        /*@ public normal_behavior
          @ requires i != null;
          @ ensures nlist == \dl_cons(i, \old(nlist));
          // @ ensures \dl_len(nlist) == \dl_len(\old(nlist)) + 1;
          @ assignable footprint;
          */
        void cons(Nat i);

        /*@ public normal_behavior
          @ ensures nlist == \dl_reverse(\old(nlist));
          @ assignable footprint;
          */
        void reverse();

        /*@ public normal_behavior
          @ ensures \result == \dl_len(nlist);
          @ assignable \strictly_nothing;
          @*/
        int length();

        /*@ public normal_behavior
          @ requires i >= 0;
          @ requires i < \dl_len(nlist);
          @ ensures \result == \dl_get(nlist, i);
          @ assignable \strictly_nothing;
          @*/
        Nat get(int i);

        /*@ public normal_behavior
          @ requires \dl_len(nlist) >= 1;
          @ requires 0 <= k && k < \dl_len(nlist);
          @ ensures nlist == \dl_remove(\old(nlist), k);
          @ assignable footprint;
          @*/
        void remove(int k);

        /*@ public normal_behavior
          @ ensures nlist == \dl_append(\old(nlist), l.nlist);
          @ assignable footprint;
          @*/
        void append(INatList l);
    }

    public class NatListImpl implements INatList {
        //@ public instance ghost \dl_NatList impl;

        //@ represents nlist = impl;
        //@ represents footprint = a, a[*], impl;

        //@ invariant a != null;
        //@ invariant a.length >= 0;

    /*@ invariant (\forall int x; 0 <= x && x < a.length; \dl_get(impl, x) == a[x]);
      @ invariant (\forall int x; 0 <= x && x < a.length; a[x] != null);
      @ invariant \dl_len(impl) == a.length;
      @ invariant \dl_len(impl) >= 0;
      @*/

        /*@ public normal_behavior
          @ ensures a != null;
          @ ensures \new_elems_fresh(footprint);
          @ ensures impl == \dl_nil();
          @ ensures 0 == \dl_len(impl);
          @ ensures \fresh(footprint);
          @ assignable footprint;
          @*/
        public /*@ pure @*/  NatListImpl() {
            //@ set impl = \dl_nil();
            a = new Nat[0];
        }

        public /*@ nonnull @*/ Nat a[];
        //int len;

        public void cons(Nat i) {
            Nat[] a_ = new Nat[a.length + 1];

        /*@ loop_invariant 1 <= idx <= a_.length;
          // @ loop_invariant a.length >= 1;
          @ loop_invariant a_.length == a.length + 1;
          @ loop_invariant (\forall int k; 1 <= k < idx; a_[k] == \old(a[k - 1]));
          @ decreases a_.length - idx;
          @ assignable a_[1 .. a_.length];
        */
            for (int idx = 1; idx < a_.length; idx++) {
                a_[idx] = a[idx - 1];
            }
            //@ set impl = \dl_cons(i, impl);
            a = a_;
            a[0] = i;
        }

        public int length() {
            return a.length;
        }

        public Nat get(int i) {
            return a[i];
        }

        public void reverse() {
            Nat[] a_ = new Nat[a.length];
        /*@ loop_invariant 0 <= i <= a.length;
          @ loop_invariant (\forall int l; 0 <= l < i; a_[l] == \old(a[a.length-l-1]));
          @ decreases a.length - i;
          @ assignable a_[*];
          @*/
            for (int i = 0; i < a.length; i++) {
                a_[i] = a[a.length - i - 1];
            }
            //@ set impl = \dl_reverse(impl);
            a = a_;
        }


        public void remove(int k) {
            Nat[] a_ = new Nat[a.length - 1];
        /*@ loop_invariant 0 <= i1 <= k;
          @ loop_invariant (\forall int i; 0 <= i < i1; a_[i] == \old(a[i]));
          @ loop_invariant (\forall int i; 0 <= i < i1; a_[i] != null);
          @ decreases k - i1;
          @ assignable a_[0 .. k - 1];
          @*/
            for (int i1 = 0; i1 < k; i1++) {
                a_[i1] = a[i1];
            }
        /*@ loop_invariant k <= i2 <= a_.length;
          @ loop_invariant (\forall int i; 0 <= i < i1; a_[i] == \old(a[i]));
          @ loop_invariant (\forall int i; i1 <= i < i2; a_[i] == \old(a[i + 1]));
          @ loop_invariant (\forall int i; 0 <= i < i2; a_[i] != null);
          @ decreases \old(a).length - 1 - i2;
          @ assignable a_[k .. (\old(a).length - 1)];
          @*/
            for (int i2 = k; i2 < a_.length; i2++) {
                a_[i2] = a[i2 + 1];
            }
            //@ set impl = \dl_remove(impl, k);
            a = a_;
        }

        public void append(INatList l) {
            Nat[] a_ = new Nat[a.length + l.length()];
            int i = 0;
            /*@ loop_invariant 0 <= i <= a.length;
              @ loop_invariant (\forall int k; 0 <= k < i; a_[k] == \old(a[k]));
              @ loop_invariant (\forall int k; 0 <= k < i; a_[k] == \old(a[k]));
              @ decreases a.length - i;
              @ assignable a_[0 .. a.length];
              @*/
            for (i = 0; i < a.length; i++) {
                a_[i] = a[i];
            }
            /*@ loop_invariant 0 <= j <= l.length();
              @ loop_invariant (\forall int k; 0 <= k < i; a_[k] == \old(a[k]));
              @ loop_invariant (\forall int k; i <= k < i+j; a_[k] == \old(l.get(k)));
              @ decreases l.length() - j;
              @ assignable a_[i .. i + l.length()];
              @*/
            for (int j = 0; j < l.length(); j++) {
                a_[i + j] = l.get(j);
            }
            // set impl = dl_append(impl, l.nlist);
            a = a_;
        }
    }


    @Test
    public void test() {
        INatList l = new NatListImpl();
        l.cons(new Nat(1));
        l.cons(new Nat(2));
        l.cons(new Nat(3));

        INatList l2 = new NatListImpl();
        l2.cons(new Nat(1));
        l2.cons(new Nat(2));
        l2.cons(new Nat(3));

        l.append(l2);
        System.out.println(l);
    }



}
