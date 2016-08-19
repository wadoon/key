public class program  
  /*@ 
    @ determines \nothing \by h;
    @ determines \result \by \nothing;
    @*/
 {
    public static int foo(int h) {
        int[] a =  new int[2];
        a[0] = h;
        return a[1];
    }
}
// JML* comment created by KeY RIFL Transformer.

