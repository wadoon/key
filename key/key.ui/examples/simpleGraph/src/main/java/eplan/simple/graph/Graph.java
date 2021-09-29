package eplan.simple.graph;

public class Graph {

    /*@ public invariant (\forall int i;(\forall int j; 0<=i && i<=j && j<edges.length && edges[i] == edges[j]; i == j));@*/
    /*@ public invariant (\forall int i; i>=0 && i<edges.length; \invariant_for(edges[i])); @*/
    final private /*@ spec_public @*/ Edge[] edges;

    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @ ensures this.edges == edges;
      @*/
    public Graph(Edge[] edges) {
        this.edges = edges;
    }

    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures (\forall Edge e;(\exists int i; i>=0 & i<edges.length; edges[i]==e);
      @                 (\exists int j; j>=0 & j<\result.length; \result[j] == e.start));
      @ ensures (\forall Edge e;(\exists int i; i>=0 & i<edges.length; edges[i]==e);
      @                 (\exists int j; j>=0 & j<\result.length; \result[j] == e.end));
      @*/
    public Node[] getAllNodes() {

        Node[] res = new Node[2* edges.length];

        /*@ loop_invariant
          @  k>=0 && k<=edges.length &&
          @  (\forall int j; j>=0 && j<k; res[2*j] == edges[j].start && res[2*j + 1] == edges[j].end);
          @ assignable res[*];
          @ decreases edges.length - k;
          @*/
        for(int k = 0; k< edges.length; k++) {
            res[2*k] = edges[k].getStart();
            res[2*k + 1] = edges[k].getEnd();
        }

        return res;
    }

    public Edge[] getAllEdgesAt(Node n) {
        return null;
    }

    public static void main(String[] args) {

    }

}
