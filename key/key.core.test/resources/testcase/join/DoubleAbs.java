public class DoubleAbs {
  //@ public normal_behavior
  //@ ensures result >= 0;
  public int doubleAbs(int num) {
    int y = 0, x = 0;

    //@ join_proc "JoinByPredicateAbstraction";
    //@ join_params "simple" : (int x, x >= 0);
    {
      if (num < 0) {
        y = -num;
      } else {
        y = num;
      }
    }

    //@ join_proc "JoinByPredicateAbstraction";
    //@ join_params "simple" : (int x, x >= 0);
    {
      if (num < 0) {
        x = -num;
      } else {
        x = num;
      }
    }

    return x + y;
  }
}
