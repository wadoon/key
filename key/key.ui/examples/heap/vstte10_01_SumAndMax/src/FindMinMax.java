class FindMinMax {

    /*@ public normal_behaviour
      @   requires a.length > 0;
      @   requires (\forall int i; 0 <= i && i < a.length; 0 <= a[i]);
      @   ensures \result == (\max int i; 0 <= i && i < a.length; a[i]);
      @   assignable \strictly_nothing;
      @*/
    public int findMax(int a[]) {
	int max = 0;
	int k = 0;
      
        /*@ loop_invariant
          @   0 <= k && k <= a.length
          @   && (k > 0 ==> (max == (\max int i; 0 <= i && i < k; a[i])))
          @   && (k == 0 ==> max == 0);
          @
          @  assignable \strictly_nothing;
          @  decreases a.length - k;
          @*/
	while(k < a.length) {
            if(max < a[k]) {
                max = a[k];
            }
            k++;
	}
        return max;
    }

    /*@ public normal_behaviour
      @   requires a.length > 0;
      @   requires (\forall int i; 0 <= i && i < a.length; 0 <= a[i]);
      @   ensures \result == (\min int i; 0 <= i && i < a.length; a[i]);
      @   assignable \strictly_nothing;
      @*/
    public int findMin(int a[]) {
	int min = 0;
	int k = 0;
      
        /*@ loop_invariant
          @   0 <= k && k <= a.length
          @   && (k > 0 ==> (min == (\min int i; 0 <= i && i < k; a[i])));
          @
          @  assignable \strictly_nothing;
          @  decreases a.length - k;
          @*/
	while(k < a.length) {
            if(k == 0 || min > a[k]) {
                min = a[k];
            }
            k++;
	}
        return min;
    }


    /*@ public normal_behaviour 
      @  requires a.length > 0;
      @  requires (\forall int i; 0<=i && i<a.length; a[i] >= 0);
      @*/
    public void test(int[] a) {
        int min, max;

        //@ normal_behaviour
        //@  ensures (\forall int k; 0<=k<a.length; a[k] >= min);
        //@  ensures (\exists int k; 0<=k<a.length; a[k] == min);
        //@  assignable \strictly_nothing;
        {
            min = findMin(a);
        }


        //@ normal_behaviour
        //@  ensures (\forall int k; 0<=k<a.length; a[k] <= max);
        //@  ensures (\exists int k; 0<=k<a.length; a[k] == max);
        {
            max = findMax(a);
        }
    }

}
