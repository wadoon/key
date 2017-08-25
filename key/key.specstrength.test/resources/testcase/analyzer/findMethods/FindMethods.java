public class FindMethods {
    //@ ghost int f_iLastRun;
    
    // Everything covered
    /*@ public normal_behavior
      @ ensures
      @      ((\exists int i; i >= 0 && i < arr.length; arr[i] == n) ==>
      @          (arr[\result] == n && \result == f_iLastRun)
      @      )
      @   && ((\forall int i; i >= 0 && i < arr.length; arr[i] != n) ==> \result == -1)
      @   ;
      @ assignable f_iLastRun;
      @*/
    public int find_strongest_post(int[] arr, int n) {
        int i = 0;
        int result = -1;
      
        //@ set f_iLastRun = i - 1;

        /*@ loop_invariant
          @      i >= 0 && i <= arr.length
          @   && i == f_iLastRun + 1
          @   && (result != -1 || (\forall int k; k >= 0 && k < i; arr[k] != n))
          @   && (result == -1 || arr[result] == n && result == i-1)
          @   ;
          @ decreases arr.length - i;
          @ assignable f_iLastRun;
          @*/
        while (result == -1 && i < arr.length) {
            //@ set f_iLastRun = i;
            if (arr[i] == n) {
                result = i;
            }

            i++;
        }

        return result;
    }

    // One "abstractly covered" fact:
    // Post condition fact: "result_1_0 = iLastRun_0"
    /*@ public normal_behavior
      @ ensures
      @      ((\exists int i; i >= 0 && i < arr.length; arr[i] == n) ==> arr[\result] == n)
      @   && ((\forall int i; i >= 0 && i < arr.length; arr[i] != n) ==> \result == -1)
      @   ;
      @*/
    public static int find_strongest_inv(int[] arr, int n) {
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
  

    // Missing facts:
    //   2x loop body fact "i = 1 + i0", that is exact change of i.
    // One fact "abstractly covered":
    //   Post condition fact: "result = i_0 - 1"
    /*@ public normal_behavior
      @ ensures
      @      ((\exists int i; i >= 0 && i < arr.length; arr[i] == n) ==> arr[\result] == n)
      @   && ((\forall int i; i >= 0 && i < arr.length; arr[i] != n) ==> \result == -1)
      @   ;
      @*/
    public static int find_stronger_post(int[] arr, int n) {
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
  
    // Two "abstractly covered" facts:
    //   Post condition fact: "result = i_0 - 1"
    //   Post condition fact: "result = -1"
    // Two uncovered facts:
    //   2x loop body fact "i = 1 + i0"
    /*@ public normal_behavior
      @ ensures \result == -1 || arr[\result] == n;
      @*/
    public static int find_stronger_inv_3(int[] arr, int n) {
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
  
    // Two "abstractly covered" facts:
    //   Post condition fact: "result = result_1_0"
    //   Post condition fact: "result = -1"
    // Four uncovered facts:
    //   2x loop body fact "i = 1 + i0"
    //   Loop body fact: "result = -1"
    //   Loop body fact: "result = i_0"
    /*@ public normal_behavior
      @ ensures \result == -1 || arr[\result] == n;
      @*/
    public static int find_stronger_inv_2(int[] arr, int n) {
        int i = 0;
        int result = -1;

        /*@ loop_invariant
          @      i >= 0 && i <= arr.length
          @   && (result != -1 || (\forall int k; k >= 0 && k < i; arr[k] != n))
          @   && (result == -1 || arr[result] == n)
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
  
    // This method is "stonger" than the above find_stronger_inv_2,
    // but for the price of an open exception branch, since i is
    // not restrained to the legal rance in arr.
    // Four "abstractly covered" facts:
    //   Post condition fact: "result = -1"
    //   Post condition fact: "result = result_1_0"
    //   Loop body fact "i = 1 + i0"
    //     (from that, we can derive "i=0" together with one part of
    //     the inv (result != -1) and result == i_0 from the path condition,
    //     which can be used to make true the second part of the inv (\forall...))
    //   Loop body fact: "result = i_0"
    // Two uncovered facts:
    //   Loop body fact "i = 1 + i0"
    //   Loop body fact: "result = -1"
    // Open exception: "arr_0 != null, but i Out of Bounds"
    /*@ public normal_behavior
      @ ensures \result == -1 || arr[\result] == n;
      @*/
    public static int find_stronger_inv_2a(int[] arr, int n) {
        int i = 0;
        int result = -1;

        /*@ loop_invariant
          @      (result != -1 || (\forall int k; k >= 0 && k < i; arr[k] != n))
          @   && (result == -1 || arr[result] == n)
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
  
    // Two uncovered facts:
    //   2x loop body fact "i = 1 + i0", that is exact change of i.
    // Four "abstractly covered" facts:
    //   Loop body fact: "result = -1"
    //   Loop body fact: "result = i_0"
    //   Post condition fact: "result = result_1_0"
    //   Post condition fact: "result = -1"
    // Open exception: "arr_0 != null, but i Out of Bounds"
    /*@ public normal_behavior
      @ ensures \result == -1 || arr[\result] == n;
      @*/
    public static int find_stronger_inv(int[] arr, int n) {
        int i = 0;
        int result = -1;

        /*@ loop_invariant
          @   (result == -1 || arr[result] == n)
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
  
    // One "abstractly covered" fact:
    //   Post condition fact: "result = -1"
    // Four uncovered facts:
    //   2x loop body fact "i = 1 + i0", that is exact change of i.
    //   Post condition fact "result = result_1_0"
    //   Loop use case fact: "arr_0[result_1_0] = n"
    // Open exception: "arr_0 != null, but i Out of Bounds"
    /*@ public normal_behavior
      @ ensures \result == -1 || arr[\result] == n;
      @*/
    public static int find_sensible_post(int[] arr, int n) {
        int i = 0;
        int result = -1;

        /*@ loop_invariant
          @      true
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
  
    // All available facts are uncovered:
    //   2x loop body fact "i = 1 + i0", that is exact change of i.
    //   Post condition fact: "result = -1"
    //   Post condition fact: "result = result_1_0"
    // Open exception: "arr_0 != null, but i Out of Bounds"
    /*@ public normal_behavior
      @ ensures true;
      @*/
    public static int find_weakest(int[] arr, int n) {
        int i = 0;
        int result = -1;

        /*@ loop_invariant
          @      true
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
