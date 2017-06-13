public class FindMethods2 {

  // Missing facts:
  // 2x loop body fact "i = 1 + i0", that is exact change of i.
  /*@ public normal_behavior
    @ ensures
    @      ((\exists int i; i >= 0 && i < arr.length; arr[i] == n) ==> arr[\result] == n)
    @   && ((\forall int i; i >= 0 && i < arr.length; arr[i] != n) ==> \result == -1)
    @   ;
    @*/
  public static int find(int[] arr, int n) {
    int i = 0;
    int result = -1;

    /*@ loop_invariant
      @      i >= 0 && i <= arr.length
      @   && (result != -1 || (\forall int k; k >= 0 && k < i; arr[k] != n))
      @   && (result == -1 || arr[result] == n && result == i-1)
      @   ;
      @ decreases arr.length - i;
      @ assignable \nothing;
      @*/
    while (result == -1 && i < arr.length) {
        if (arr[i] == n) {
          result = i;
        }

        i++;
    }

    return result;
  }

}
