public class ArrSum {
  /*@ public normal_behavior
    @ requires arr != null;
    @ ensures (\forall int n; n >= 0 && n < arr.length;
    @            \result[n] == (\sum int k; 0 <= k && k < n; arr[k]));
    @*/
  public static final int[] arrSumStd(int[] arr) {
    int[] result = new int[arr.length];

    /*@ loop_invariant
      @      i >= 0 && i <= arr.length
      @   && (\forall int n; n >= 0 && n < i;
      @        result[n] == (\sum int k; 0 <= k && k < n; arr[k]));
      @ decreases arr.length - i;
      @ assignable result[*];
      @*/
    for (int i = 0; i < arr.length; i++) {
      int res = 0;

      /*@ loop_invariant
        @      j >= 0 && j <= i
        @   && res == (\sum int k; 0 <= k && k < j; arr[k]);
        @ decreases i - j;
        @ assignable res;
        @*/
      for (int j = 0; j < i; j++) {
        res += arr[j];
      }

      result[i] = res;
    }

    return result;
  }
}