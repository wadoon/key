package eplan.simple.graph;

public final class Node {

    /*@ model boolean mod_equals(nullable Object o) {return (o instanceof Node) && ((Node)o).id == id; } @*/

    //@ public model \locset footprint;
    //@ public accessible footprint: footprint;
    //@ public accessible \inv: footprint;
    public /*@ spec_public @*/ int id;

    /*@ public invariant \subset(this.footprint, this.*); @*/

    //@ private represents footprint = \singleton(id);

    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures this.id == p_id;
      @*/
    public Node(int p_id) {
        this.id = p_id;
    }

    /*@ public normal_behavior
     @ assignable \strictly_nothing;
     @ accessible this.id;
     @ ensures \result == this.id;
     @*/
    public int getId() {
        return id;
    }

    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @ accessible ((Node)o).id, this.id;
      @ ensures \result == ((o instanceof Node) && ((Node)o).id == id);
      @*/
    public boolean equals(/*@ nullable @*/Object o) {
        return (o instanceof Node) && ((Node)o).id == id;
    }

    
    public String toString() {
        return "Node{" +
                "id=" + id +
                '}';
    }
}
