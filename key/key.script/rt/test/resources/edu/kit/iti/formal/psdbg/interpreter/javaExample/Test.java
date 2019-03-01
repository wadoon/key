public class Test{



    /*@ public normal_behavior
      @ requires x >= 0;
      @ ensures \result >0;
      @*/
    public int foo(int x){
        if(x > 0){
            x--;
        }else{
            x++;
        }
        return x++;
    }
}