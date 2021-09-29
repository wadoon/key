package eplan.simple.graph;

public final class Node {

    /* public invariant (\forall Node n; n.id == this.id; n == this); */

    final private /*@ spec_public @*/ int id;

    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @ ensures this.id == id;
      @*/
    public Node(int id) {
        this.id = id;
    }

    /*@ public normal_behavior
     @ assignable \strictly_nothing;
     @ ensures \result == this.id;
     @*/
    public int getId() {
        return id;
    }
}
