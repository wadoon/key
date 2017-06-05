public class SimpleMath {
    
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