public class FindMethods {
  private int result;
  private int i;

  /*@ public normal_behavior
    @ ensures
    @   //true
    @      ((\exists int k; k >= 0 && k < arr.length; arr[k] == n) ==> arr[result] == n && result == i - 1)
    @   && ((\forall int k; k >= 0 && k < arr.length; arr[k] != n) ==> result == -1)
    @ ;
    @ assignable result, i;
    @*/
  public void find_instance_strong(int[] arr, int n) {
    i = 0;
    result = -1;

    //@ ghost int iLastRun = i - 1;

    /*@ loop_invariant
      @   //true
      @      i >= 0 && i <= arr.length
      @   && i == iLastRun + 1
      @   && (arr[i] == n ==> i == iLastRun + 1)
      @   && (result != -1 || (\forall int k; k >= 0 && k < i; arr[k] != n))
      @   && (result == -1 || arr[result] == n && result == i-1)
      @   ;
      @ decreases arr.length - i;
      @ assignable result, i;
      @*/
    while (result == -1 && i < arr.length) {
        //@ set iLastRun = i;
        if (arr[i] == n) {
          result = i;
        }

        i++;
    }
  }

  /*@ public normal_behavior
    @ ensures
    @   //true
    @      ((\exists int i; i >= 0 && i < arr.length; arr[i] == n) ==> arr[result] == n)
    @   && ((\forall int i; i >= 0 && i < arr.length; arr[i] != n) ==> result == -1)
    @ ;
    @ assignable result;
    @*/
  public void find_instance(int[] arr, int n) {
    int i = 0;
    int result = -1; //TODO The analyzer thinks this method's 100% strong if we directly use the field.

    //@ ghost int iLastRun = i - 1;

    /*@ loop_invariant
      @   //true
      @      i >= 0 && i <= arr.length
      @   && i == iLastRun + 1
      @   && (arr[i] == n ==> i == iLastRun + 1)
      @   && (result != -1 || (\forall int k; k >= 0 && k < i; arr[k] != n))
      @   && (result == -1 || arr[result] == n && result == i-1)
      @   ;
      @ decreases arr.length - i;
      @ assignable result;
      @*/
    while (result == -1 && i < arr.length) {
        //@ set iLastRun = i;
        if (arr[i] == n) {
          result = i;
        }

        i++;
    }

    this.result = result;
  }

  /*@ public normal_behavior
    @ ensures
    @   //\result == -1 || arr[\result] == n
    @      ((\exists int i; i >= 0 && i < arr.length; arr[i] == n) ==> arr[\result] == n)
    @   && ((\forall int i; i >= 0 && i < arr.length; arr[i] != n) ==> \result == -1)
    @   ;
    @*/
  public static int find_strong(int[] arr, int n) {
    int i = 0;
    int result = -1;

    //@ ghost int iLastRun = i - 1;

    /*@ loop_invariant
      @   //true
      @      i >= 0 && i <= arr.length
      @   && i == iLastRun + 1
      @   && (arr[i] == n ==> i == iLastRun + 1)
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

  /*@ public normal_behavior
    @ ensures
    @   //\result == -1 || arr[\result] == n
    @      ((\exists int i; i >= 0 && i < arr.length; arr[i] == n) ==> arr[\result] == n)
    @   && ((\forall int i; i >= 0 && i < arr.length; arr[i] != n) ==> \result == -1)
    @   ;
    @*/
  public static int find(int[] arr, int n) {
    int i = 0;
    int result = -1;

    /*@ loop_invariant
      @   //true
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
