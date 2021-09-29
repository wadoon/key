package eplan.simple.graph;

public final class Edge {

    /*@ public invariant (\forall Edge e; e.id == this.id; e == this); @*/
    /*@ public invariant \invariant_for(start) && \invariant_for(end); @*/

    final private /*@ spec_public @*/ int id;
    final private /*@ spec_public @*/ Node start;
    final private /*@ spec_public @*/ Node end;

    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @ ensures this.id == id;
      @ ensures this.start == start;
      @ ensures this.end == end;
      @*/
    public Edge(int id, Node start, Node end) {
        this.id = id;
        this.start = start;
        this.end = end;
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
