public class FindMethods {
  //@ ghost int g_i;
  //@ ghost int iLastRun;
    
  /*@ public normal_behavior
    @ ensures
    @      ((\exists int k; k >= 0 && k < arr.length; arr[k] == n) ==> arr[\result] == n && \result == g_i - 1)
    @   && ((\forall int k; k >= 0 && k < arr.length; arr[k] != n) ==> \result == -1)
    @   && g_i >= 0
    @   && g_i == iLastRun + 1 // TODO check if these formulas improve anything
    @ ;
    @ assignable g_i, iLastRun;
    @*/
  public int find_strongest(int[] arr, int n) {
    int i = 0;
    int result = -1;
    //@ set g_i = i;
    //@ set iLastRun = i - 1;

    /*@ loop_invariant
      @      i >= 0 && i <= arr.length
      @   && g_i == i
      @   && i == iLastRun + 1
      @   && (result != -1 || (\forall int k; k >= 0 && k < i; arr[k] != n))
      @   && (result == -1 || arr[result] == n && result == i-1)
      @   ;
      @ decreases arr.length - i;
      @ assignable g_i, iLastRun;
      @*/
    while (result == -1 && i < arr.length) {
        //@ set iLastRun = i;
        //@ set g_i = i;
        if (arr[i] == n) {
          result = i;
        }

        i++;
        //@ set g_i = i;
        {}
    }
    
    return result;
  }
  
  // This method is only missing the fact that "i >= 0", which can be provided
  // by just adding it to the post condition.

  /*@ public normal_behavior
    @ ensures
    @      ((\exists int k; k >= 0 && k < arr.length; arr[k] == n) ==> arr[\result] == n && \result == g_i - 1)
    @   && ((\forall int k; k >= 0 && k < arr.length; arr[k] != n) ==> \result == -1)
    @ ;
    @ assignable g_i, iLastRun;
    @*/
  public int find_stronger(int[] arr, int n) {
    int i = 0;
    int result = -1;
    //@ set g_i = i;
    //@ set iLastRun = i - 1;

    /*@ loop_invariant
      @      i >= 0 && i <= arr.length
      @   && g_i == i
      @   && i == iLastRun + 1
      @   && (result != -1 || (\forall int k; k >= 0 && k < i; arr[k] != n))
      @   && (result == -1 || arr[result] == n && result == i-1)
      @   ;
      @ decreases arr.length - i;
      @ assignable g_i, iLastRun;
      @*/
    while (result == -1 && i < arr.length) {
      //@ set iLastRun = i;
      //@ set g_i = i;
      if (arr[i] == n) {
        result = i;
      }

      i++;
      //@ set g_i = i;
      {}
    }
  
    return result;
  }

  // This covers the fact of "find"
  //   i = 1 + i_0            (loop body fact)
  // but, since now the invariant is stronger than what the post condition
  // can reason about, adds 3 additional "post condition -> invariant" facts.
  //
  // Note: Among the 3 is the previously closed "i >= 0", since a formula
  // "!i_0 < arr_0.length" is replaced by "1 + iLastRun_0 < arr_0.length" and
  // the post condition does not provide additional knowledge about iLastRun.
  
  /*@ public normal_behavior
    @ ensures
    @      ((\exists int i; i >= 0 && i < arr.length; arr[i] == n) ==> arr[\result] == n)
    @   && ((\forall int i; i >= 0 && i < arr.length; arr[i] != n) ==> \result == -1)
    @   ;
    @*/
  public static int find_strong_inv(int[] arr, int n) {
    int i = 0;
    int result = -1;

    //@ ghost int iLastRun = i - 1;

    /*@ loop_invariant
      @      i >= 0 && i <= arr.length
      @   && i == iLastRun + 1
      @   && (result != -1 || (\forall int k; k >= 0 && k < i; arr[k] != n))
      @   && (result == -1 || arr[result] == n && result == i-1)
      @   ;
      @ decreases arr.length - i;
      @ assignable \nothing;
      @*/
    while (result == -1 && i < arr.length) {
        //@ set iLastRun = i;
        if (arr[i] == n) {
          result = i;
        }

        i++;
    }

    return result;
  }

  // Missing facts (all but the last two "post condition -> invariant" facts):
  // (2x) i == arr.length        (titled "result_1 != -1" in the proof)
  // (2x) i <= arr.length
  // (1x) i >= 0                 (for the case that n wasn't found)
  // (2x) result_1_0 = i_0 - 1   (titled "result_1 = -1 | ..." in the proof, for the case that n was found - two cases due to CNF conversion)
  // (2x) i = 1 + i_0            (loop body fact)
  // (1x) result = i_0 - 1       (post condition fact -- for the case that n was found
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

  // This method adds a second post condition weakness to those of 
  // the "find" method:
  //
  // "result = -1" for the case where n was not found
  
  /*@ public normal_behavior
    @ ensures
    @   \result == -1 || arr[\result] == n
    @   ;
    @*/
  public static int find_weak_postcond(int[] arr, int n) {
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
