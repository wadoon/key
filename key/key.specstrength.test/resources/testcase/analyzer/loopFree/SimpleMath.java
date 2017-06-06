public class SimpleMath {
    
    /*@ public normal_behavior
      @ ensures    (num < 0  ==> \result == -num) 
      @         && (num >= 0 ==> \result == num);
      @*/
    public static int abs_strongest(int num) {
        if (num < 0)
            return num * -1;
        else
            return num;
    }
    
    /*@ public normal_behavior
      @ ensures (num >= 0 ==> \result == num);
      @*/
    public static int abs_stronger_3(int num) {
        if (num < 0)
            return num * -1;
        else
            return num;
    }
    
    /*@ public normal_behavior
      @ ensures (num < 0 ==> \result == -num);
      @*/
    public static int abs_stronger_2(int num) {
        if (num < 0)
            return num * -1;
        else
            return num;
    }
    
    /*@ public normal_behavior
      @ ensures \result >= 0;
      @*/
    public static int abs_stronger_1(int num) {
        if (num < 0)
            return num * -1;
        else
            return num;
    }
    
    /*@ public normal_behavior
      @ ensures true;
      @*/
    public static int abs(int num) {
        if (num < 0)
            return num * -1;
        else
            return num;
    }
    
}