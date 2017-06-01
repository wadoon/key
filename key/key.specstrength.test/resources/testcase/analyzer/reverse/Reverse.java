public class Reverse {

  /*@ public normal_behavior
    @ ensures (\forall int i; i >= 0 && i < arr.length; \result[arr.length - i - 1] == arr[i]);
    @*/
  public static int[] reverse(int[] arr) {
	  int[] result = new int[arr.length];

	  int i = arr.length - 1;
	  int k = 0;

	  // if "k == arr.length - i - 1" is left out, then after some
	  // frickling around with the proof tree, we get the proof
	  // obligation "-1 + i_2 * -1 + arr_0.length <= -1 + k_0" which
	  // is implied by this. However, we only get this proof obligation
	  // if we interact with the proof, otherwise the antecedent formula
	  // this originates from is simplified away, since it's essentially
	  // false (without the additional knowledge).

	  /*@ loop_invariant
	    @ 	   i + 1 >= 0 && i < arr.length && k >= 0 && k <= arr.length
	    @   && k == arr.length - i - 1
	    @   && (\forall int j; j >= 0 && j < k; result[j] == arr[arr.length - j - 1])
	    @   ;
	    @   //true;
	    @ decreases i + 1;
	    @ assignable result[*];
	    @*/
	  while (i >= 0) {
		  result[k] = arr[i];
		  i--; k++;
	  }

	  return result;
  }

}
