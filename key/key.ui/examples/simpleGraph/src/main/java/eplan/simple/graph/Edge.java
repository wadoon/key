package eplan.simple.graph;

public final class Edge {

    //@ public model \locset footprint;
    //@ public accessible footprint: footprint;
    //@ public accessible \inv: footprint;

    /*@ public invariant \subset(this.footprint, \set_union(this.*, \set_union(start.footprint, end.footprint))); @*/
    /*@ public invariant \invariant_for(start) && \invariant_for(end); @*/
    /*@ public invariant length >= 0; @*/
    final private /*@ spec_public @*/ int id;
    final private /*@ spec_public @*/ Node start;
    final private /*@ spec_public @*/ Node end;
    final private /*@ spec_public @*/ int length;

    //@ private represents footprint = id, start, end, length, start.footprint, end.footprint;

    /*@ public normal_behavior
      @ requires \invariant_for(start) && \invariant_for(end);
      @ assignable \nothing;
      @ ensures this.id == id;
      @ ensures this.start == start;
      @ ensures this.end == end;
      @ ensures this.length == 0;
      @*/
    public Edge(Node start, Node end, int id) {
        this.id = id;
        this.start = start;
        this.end = end;
        this.length = 0;
    }


    /*@ public normal_behavior
      @ requires \invariant_for(start) && \invariant_for(end);
      @ requires len >= 0;
      @ assignable \nothing;
      @ ensures this.id == id;
      @ ensures this.start == start;
      @ ensures this.end == end;
      @ ensures this.length == len;
      @*/
    public Edge(Node start, Node end, int id, int len) {
        this.id = id;
        this.start = start;
        this.end = end;
        this.length = len;
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
    public int getId() {
        return id;
    }

    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @ accessible this.start;
      @ ensures \result == this.start;
      @*/
    public Node getStart() {
        return start;
    }

    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @ accessible this.end;
      @ ensures \result == this.end;
      @*/
    public Node getEnd() {
        return end;
    }

    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @ accessible this.length;
      @ ensures \result == this.length;
      @*/
    public int getLength() {
        return length;
    }

    public String toString() {
        return "Edge{" +
                "id=" + id +
                ", start=" + start +
                ", end=" + end +
                ", length=" + length +
                '}';
    }
}