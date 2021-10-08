package eplan.simple.graph;

public final class Node {

    /* public invariant (\forall Node n; n.id == this.id; n == this); */

    final private /*@ spec_public @*/ int id;

    /*@ public normal_behavior
      @ requires (\forall Node n; n.id != p_id);
      @ assignable \nothing;
      @ ensures this.id == p_id;
      @*/
    public Node(int p_id) {
        this.id = p_id;
    }

    /*@ public normal_behavior
     @ assignable \strictly_nothing;
     @ ensures \result == this.id;
     @*/
    public int getId() {
        return id;
    }
}
