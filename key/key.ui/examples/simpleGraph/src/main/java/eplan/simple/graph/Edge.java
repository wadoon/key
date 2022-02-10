package eplan.simple.graph;

public final class Edge {

    /*@ public invariant \invariant_for(start) && \invariant_for(end); @*/
    //@ accessible \inv: start, end;
    final private /*@ spec_public @*/ int id;
    final private /*@ spec_public @*/ Node start;
    final private /*@ spec_public @*/ Node end;

    /*@ public normal_behavior
      @ requires \static_invariant_for(Edge);
      @ assignable \nothing;
      @ ensures this.id == id;
      @ ensures this.start == start;
      @ ensures this.end == end;
      @*/
    public Edge(Node start, Node end, int id) {
        this.id = id;
        this.start = start;
        this.end = end;
    }

    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @ accessible ((Edge)o).id, this.id, this.start, this.end;
      @ ensures \result == ((o instanceof Edge) && ((Edge)o).id == id);
      @*/
    public boolean equals(Object o) {
        if (!(o instanceof Edge)) {
            return false;
        }
        return ((Edge)o).id == id;
    }

    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @ accessible this.id;
      @ ensures \result == this.id;
      @*/
    public /*@ helper @*/ int getId() {
        return id;
    }

    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @ accessible this.start;
      @ ensures \result == this.start;
      @*/
    public /*@ helper @*/ Node getStart() {
        return start;
    }

    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @ accessible this.end;
      @ ensures \result == this.end;
      @*/
    public /*@ helper @*/ Node getEnd() {
        return end;
    }

    public String toString() {
        return "Edge{" +
                "id=" + id +
                ", start=" + start +
                ", end=" + end +
                '}';
    }
}
