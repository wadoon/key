public class DualTypeTest {

    //@ ghost \real r;
    // \bigint

    //@ normal_behaviour
    //@  ensures r == \old(r) + 1.r;
    void m1() {
        //@ set r = r+1;
        {
        }
    }

    /*@ public normal_behaviour
      @  requires true;
      @  ensures 5.r == 50e-1r;
      @*/
    void m2() {
    }

    /*@ public normal_behaviour
      @  requires true;
      @  ensures 5.r > 0.r;
      @*/
    void m3() {
    }
}