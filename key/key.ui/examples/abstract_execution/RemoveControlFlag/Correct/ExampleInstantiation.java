public class ExampleInstantiation {
    /*@ public normal_behavior
      @ ensures \result == -1 || arr[\result] == elem;
      @*/
    public int linearSearch(int[] arr, int elem) {
        boolean done = false;
        int i = 0;
        int result = -1;

        // loopLocs := i, result, arr[*], arr.length, elem
        // decrExpr := arr.length - i
        // loopInv := i >= 0 && i <= arr.length &&
        //              (\forall int j; j >= 0 && j < i-1; arr[j] != elem) &&
        //              (result != -1 <==> (i > 0 && arr[i-1] == elem && result == i-1))
        // guardVal := i < arr.length
        // doneCondition := done <==> (i > 0 && arr[i-1] == elem)

        /*@ loop_invariant i >= 0 && i <= arr.length &&
          @   (done <==> (i > 0 && arr[i-1] == elem)) &&
          @   (\forall int j; j >= 0 && j < i-1; arr[j] != elem) &&
          @   (result != -1 <==> (i > 0 && arr[i-1] == elem && result == i-1));
          @ decreases arr.length - i;
          @ assignable arr[*]; // actually too weak
          @*/
        while (!done && i < arr.length) {
            if (arr[i] == elem) {
                done = true;
                result = i;
            }

            i++;
        }

        return result;
    }

    /*@ public normal_behavior
      @ ensures \result == -1 || arr[\result] == elem;
      @*/
    public int linearSearchTransf(int[] arr, int elem) {
        int i = 0;
        int result = -1;

        // loopLocs := i, result, arr[*], arr.length, elem
        // decrExpr := arr.length - i
        // loopInv := i >= 0 && i <= arr.length &&
        //              (\forall int j; j >= 0 && j < i-1; arr[j] != elem) &&
        //              (result != -1 <==> (i > 0 && arr[i-1] == elem && result == i-1))
        // guardVal := i < arr.length
        // doneCondition := done <==> (i > 0 && arr[i-1] == elem)

        /*@ loop_invariant i >= 0 && i <= arr.length &&
          @   !(i > 0 && arr[i-1] == elem) &&
          @   (\forall int j; j >= 0 && j < i-1; arr[j] != elem) &&
          @   (result != -1 <==> (i > 0 && arr[i-1] == elem && result == i-1));
          @ decreases arr.length - i;
          @ assignable arr[*]; // actually too weak
          @*/
        while (i < arr.length) {
            if (arr[i] == elem) {
                result = i;
                i++;
                break;
            }

            i++;
        }

        return result;
    }
}
