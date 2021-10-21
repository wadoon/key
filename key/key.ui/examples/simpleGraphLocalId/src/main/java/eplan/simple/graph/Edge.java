package eplan.simple.graph;

public final class Edge {

    /*@ public static invariant (\forall Edge e; e.id < ID); @*/
    private static int ID = 0;

    /*@ public invariant (\forall Edge e; e.id == this.id; e == this); @*/
    /*@ public invariant \invariant_for(start) && \invariant_for(end); @*/
    final private /*@ spec_public @*/ int id;
    final private /*@ spec_public @*/ Node start;
    final private /*@ spec_public @*/ Node end;

    /*@ public normal_behavior
      @ requires \static_invariant_for(Edge);
      @ assignable ID;
      @ ensures this.id == \old(ID);
      @ ensures this.start == start;
      @ ensures this.end == end;
      @*/
    public Edge(Node start, Node end) {
        this.id = ID++;
        this.start = start;
        this.end = end;
    }
    public boolean equals(Object o) {
        if (!(o instanceof Edge)) {
            return false;
        }
        return ((Edge)o).id == id;
    }

    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @ ensures \result == this.id;
      @*/
    public int getId() {
        return id;
    }

    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @ ensures \result == this.start;
      @*/
    public Node getStart() {
        return start;
    }

    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @ ensures \result == this.end;
      @*/
    public Node getEnd() {
        return end;
    }
}
