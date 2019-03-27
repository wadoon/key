 public final class Simple {
 
 
    boolean b1;
    boolean b2;
    
    /*@ public normal_behavior
      @ ensures \dl_seqPerm(\dl_array2seq(\result), \old(\dl_array2seq(aarr)));
      @ assignable \everything;
     */
    public int[] transitive(int[] aarr){
        aarr = Simple.copyArray(aarr); 
        sort(aarr); 
        int[] barr = Simple.copyArray(aarr);
        
        if(b1){barr = Simple.copyArray(aarr);} 
        if(b2){log(barr);}
        return barr;
    }

    /*@ public normal_behavior
      @ ensures \dl_seqPerm(\dl_array2seq(a), \old(\dl_array2seq(a)));
      @ assignable a[*];
      */
    public void sort(int[] a){};

    /*@ public normal_behavior
      @ ensures (\forall int i; 0 <= i < input.length; input[i] == \result[i]) 
      @ && \result.length == input.length;
      @ ensures \fresh(\result);
      @ ensures \dl_seqPerm(\dl_array2seq(\result), \dl_array2seq(input));
      @ assignable \nothing;
      */
    public /*@helper@*/ static int[] copyArray(int[] input){}

    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      */
    public void log(int[] a){};

}
