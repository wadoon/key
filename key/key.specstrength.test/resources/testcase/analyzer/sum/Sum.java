public class Sum {

  /*@ public normal_behavior
    @ ensures
    @   \result == (\sum int i; 0 <= i && i < arr.length; arr[i]);
    @*/
  public static int sum(int[] arr) {
    int result = 0, i = 0;

    // If the \sum expression is missing in the invariant,
    // then the fact "result_1 = result_1_0 + arr[i_0]" is
    // not covered.
    // Question: Can we prove that the \sum, if it's there,
    // implies this fact?

    // If only the \sum expression is present, then there is
    // one open branches (exception) with path conditions
    // "i_0 < 0" the invariant does not talk about. Also,
    // the use case cannot be proven, since i could be too big;
    // in the proof, this is reflected in the fact that there is
    // a precondition "i < arr.length" not covered by the invariant.

    /*@ loop_invariant
      @   i >= 0 && i <= arr.length && result == (\sum int k; 0 <= k && k < i; arr[k]);
      @   //i >= 0 && i <= arr.length;
      @   //result == (\sum int k; 0 <= k && k < i; arr[k]);
      @ decreases arr.length - i;
      @ assignable \nothing;
      @*/
    while (i < arr.length) {
        result += arr[i];
        i++;
    }

    return result;
  }

}
