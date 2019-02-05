package java.lang;

public class System {

    public static final java.io.InputStream in;
    public static final java.io.PrintStream out;
    public static final java.io.PrintStream err;
    
    // remarks: assume src and dest to be int[], src != dest, no exceptional
    // -> should be enough for our use case
    /*@ public normal_behavior
      @ requires src instanceof int[] && dest instanceof int[];
      @ requires src != dest;
      @ requires srcPos >= 0 && destPos >= 0;
      @ requires length >= 0;
      @ requires srcPos + length <= ((int[])src).length && destPos + length <= ((int[])dest).length;
      @ ensures (\forall int i; 0 <= i && i < length;
      @             ((int[])dest)[destPos + i] == ((int[])src)[srcPos + i]);
      @ assignable \strictly_nothing;
      @*/
    public static native void arraycopy(Object src,  int  srcPos,
                                        Object dest, int destPos,
                                        int length);



}
