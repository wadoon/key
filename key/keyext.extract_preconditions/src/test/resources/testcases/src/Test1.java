public class Test1{

    /*@ public normal_behavior
      @  ensures \result!=0;
      @*/
    public  int test1(int x, int y){
        if (x >= 0) {
            x = 0;
        } else if (y <= 0) {
            y = 0;
        }
        return x*y;
    }

}
