package eplan.simple.graph;

public class Test {
    int val;

    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @ ensures \result == val;
      @*/
    int getVal() {
        return val;
    }

    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @ ensures \result == val + 1;
      @*/
    int m() {
        return this.getVal() + 1;
    }
}
