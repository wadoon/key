package eplan.simple.graph;

public class EdgeList {

    /*@ public model \seq list; @*/
    /*@ public model \locset footprint; @*/

    /*@ public invariant array.length > firstFreeIndex; @*/
    /*@ public invariant list.length == firstFreeIndex; @*/
    /*@ public invariant array != null; @*/
    /*@ public invariant (\forall int i; i >= 0 && i < firstFreeIndex; array[i] != null); @*/
    /*@ public invariant \typeof(array) == \type(Edge[]); @*/

    private /*@ nullable @*/ Edge[] array;
    private int firstFreeIndex = 0;

    /* public represents list = (\seq_def int i; 0; firstFreeIndex; array[i]); @*/
    /*@ public represents list = \dl_array2seq(array)[0..firstFreeIndex]; @*/
    /*@ public represents footprint = array, array[*], firstFreeIndex; @*/
    //@ accessible list:footprint;
    //@ accessible footprint:footprint;
    //@ accessible \inv:footprint;


    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures firstFreeIndex == 0;
      @*/
    public EdgeList() {
        array = new Edge[10];
        firstFreeIndex = 0;
    }


    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @ ensures \result == list.length;
      @*/
    public /*@ strictly_pure @*/ int size() {
        return firstFreeIndex;
    }


    /*@ public normal_behavior
      @ requires \invariant_for(n);
      @ ensures list == \seq_concat(\old(list), \seq_singleton(n));
      @ assignable footprint;
      @*/
    public void add (Edge n) {
        if(array.length > firstFreeIndex + 1) {
            array[firstFreeIndex] = n;
        }
        else {
            int newLength = array.length + 10;
            Edge[] newArray = new Edge[newLength];
            /*@ loop_invariant
              @ i >= 0 && i <= array.length &&
              @ (\forall int j; 0 <= j && j < i; newArray[j] == \old(array[j]));
              @ assignable newArray[*];
              @ decreases array.length - i;
              @*/
            for (int i = 0; i < array.length; i++) {
                newArray[i] = array[i];
            }
            newArray[firstFreeIndex] = n;
            array = newArray;
        }
        firstFreeIndex++;
    }


    /*@ public normal_behavior
      @ requires i >= 0 && i < list.length;
      @ ensures \result == list[i];
      @ assignable \strictly_nothing;
      @*/
    public /*@ strictly_pure @*/ Edge get (int i) {
        return array[i];
    }


    /*@ public normal_behavior
      @ requires \invariant_for(n);
      @ ensures \result == (\exists int i; i >= 0 && i < list.length; ((Edge) list[i]).equals(n));
      @ assignable \strictly_nothing;
      @*/
    public /*@ strictly_pure @*/ boolean contains (Edge n) {
        if(getIndex(n) >= 0) {
            return true;
        }
        return false;
    }


    /*@ public normal_behavior
      @ requires \invariant_for(n);
      @ ensures (\exists int i; i >= 0 && i < list.length; ((Edge) list[i]).equals(n)) ? \result >= 0 && \result < list.length && ((Edge) list[\result]).equals(n) : \result == -1;
      @ assignable \strictly_nothing;
      @*/
    public /*@ strictly_pure @*/ int getIndex (Edge n) {
        /*@ loop_invariant
          @ i >= 0 && i <= firstFreeIndex &&
          @ (\forall int j; 0 <= j && j < i; !array[j].equals(n));
          @ assignable \strictly_nothing;
          @ decreases firstFreeIndex - i;
          @*/
        for (int i = 0; i < firstFreeIndex; i++) {
            if (array[i].equals(n)) {
                return i;
            }
        }
        return -1;
    }


    /*@ public normal_behavior
      @ requires i >= 0 && i < list.length;
      @ ensures list == \seq_concat(\old(list[0..i]), \old(list[i+1..list.length]));
      @ assignable array[*], firstFreeIndex;
      @*/
    public void remove (int i) {
        /*@ loop_invariant
          @ j >= i && j <= array.length - 1 &&
          @ (\forall int k; 0 <= k && k < i; array[k] == \old(array[k])) &&
          @ (\forall int l; i <= l && l < j; array[l] == \old(array[l+1])) &&
          @ (\forall int k; j <= k && k < array.length; array[k] == \old(array[k]));
          @ assignable array[*];
          @ decreases array.length - j;
          @*/
        for (int j = i; j < array.length - 1; j++) {
            array[j] = array[j+1];
        }
        array[array.length - 1] = null;
        firstFreeIndex--;
    }


    public String toString() {

        String returnval = "[";
        for (int i = 0; i < firstFreeIndex; i++) {
            returnval += array[i];
            if (i < firstFreeIndex - 1) {
                returnval += ",";
            }
        }
        returnval += "]";
        return returnval;
    }
}