package eplan.simple.graph;

public class Graph {

    /*@ public invariant (\forall int i;(\forall int j; 0<=i && i<=j && j<edges.length && edges[i] == edges[j]; i == j));@*/
    /*@ public invariant (\forall int i; i>=0 && i<edges.length; \invariant_for(edges[i])); @*/

    /*@ public invariant (\forall int i;(\forall int j; 0<=i && i<=j && j<edges.length && edges[i].id == edges[j].id; i == j));@*/

    /*
      1. aktuelle Loesung mit Schleifeninvariante wiederholt Teil der Objektinvariante (\forall int i; i>=0 && i<edges.length; \invariant_for(edges[i]))
      2. Globale ID Vergabe und Auslagerung der Eindeutigkeit der ID aus Edge (und Node)
      3. Geisterfeld mit Collection aller bereits vergebenenen IDs (oder fuer Verifikation vermutl. einfacher aller erzeugten Edges)
      4. JML Erweiterung, die es erlaubt im assignable die Erzeugung bestimmter Typen von Objekten auszuschliessen
     */

    final private /*@ spec_public @*/ Edge[] edges;

    /*@ public normal_behavior
      @ requires (\forall int i;(\forall int j; 0<=i && i<=j && j<edges.length && edges[i].id == edges[j].id; i == j));
      @ requires (\forall int i;(\forall int j; 0<=i && i<=j && j<edges.length && edges[i] == edges[j]; i == j));
      @ requires (\forall int i; i>=0 && i<edges.length; \invariant_for(edges[i]));
      @ assignable \nothing;
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
        for(int k = 0; k<edges.length; k++) {
            res[2*k] = edges[k].getStart();
            res[2*k + 1] = edges[k].getEnd();
        }

        return res;
    }

    /*@ public normal_behavior
      @ requires dir && \invariant_for(e);
      @ assignable \nothing;
      @ ensures \result != null && \result.length == 2*edges.length;
      @ ensures (\forall int j; j >= 0 && j < \result.length;
                    \result[j] == null || \result[j].getStart() == e.getEnd() || \result[j].getEnd() == e.getEnd());
      @*/
    public /*@ nullable @*/ Edge[] getNeighborEdges(Edge e, boolean dir) {
        Edge[] returnval = new Edge[2*edges.length];
        int pos = 0;
        Node connectedNode;
        if(dir) {
            connectedNode = e.getEnd();
        }
        else {
            connectedNode = e.getStart();
        }

        // merge_point
        // merge_proc "MergeByPredicateAbstraction"
        // merge_params {conjunctive: (Node n) -> {n != null, n == e.getEnd() || n == e.getStart()}};
        ;

        /*@ loop_invariant
          @ i >= 0 && i <= edges.length && pos >= 0 && pos <= 2*i &&
          @  (\forall int j; j >= 0 && j < pos;
          @          returnval[j].getStart() == e.getEnd() || returnval[j].getEnd() == e.getEnd()) &&
          @  (\forall int j; j >= pos && j < returnval.length;
          @          returnval[j] == null);
          @ assignable returnval[*];
          @ decreases edges.length - i;
          @*/
        for (int i = 0; i < edges.length; i++) {
            Edge tempEdge = edges[i];
            Node startNode = tempEdge.getStart();
            Node endNode = tempEdge.getEnd();

            //@ ghost int oldPos = pos;
            //@ ghost Edge oldE = returnval[pos];
            //@ ghost Edge oldE1 = returnval[pos + 1];

            /*@ normal_behavior
              @ requires returnval != null && startNode != null && endNode != null && connectedNode != null
                              && pos >= 0 && pos + 1 < returnval.length;
              @ assignable returnval[pos..pos+1];
              @ ensures (pos == oldPos) ==> (returnval[pos] == oldE) &&
              @                               (returnval[pos+1] == oldE1);
              @ ensures (pos > oldPos) ==>  (\forall int j; j >= oldPos && j < pos; returnval[j] == tempEdge);
              @ ensures pos >= oldPos && pos <= oldPos + 2;
              @*/
            {
                if (startNode.equals(connectedNode)) {
                    returnval[pos] = tempEdge;
                    pos++;
                }
                // merge_point
                // merge_proc "MergeByIfThenElse";
                ;
                if (endNode.equals(connectedNode)) {
                    returnval[pos] = tempEdge;
                    pos++;
                }
                // merge_point
                // merge_proc "MergeByIfThenElse";
                ;
            }
        }
        return returnval;
        //return getNeighborsForConnectedNode(connectedNode);
    }

    /*@ public normal_behavior
      @ requires \invariant_for(connectedNode);
      @ assignable \nothing;
      @ ensures \result != null && \result.length == 2*edges.length;
      @*/
    private /*@ nullable @*/ Edge[] getNeighborsForConnectedNode(Node connectedNode) {
        Edge[] returnval = new Edge[2*edges.length];
        int pos = 0;

        /*@ loop_invariant
          @ i >= 0 && i <= edges.length && pos >= 0 && pos <= 2*i;
          @ assignable returnval[*];
          @ decreases edges.length - i;
          @*/
        for (int i = 0; i < edges.length; i++) {
            Edge tempEdge = edges[i];
            Node startNode = tempEdge.getStart();
            Node endNode = tempEdge.getEnd();
            if (startNode.equals(connectedNode)) {
                returnval[pos] = tempEdge;
                pos++;
            }
            if (endNode.equals(connectedNode)) {
                returnval[pos] = tempEdge;
                pos++;
            }
        }
        return returnval;
    }


    /* public normal_behavior
      @ requires \invariant_for(n);
      @ assignable \nothing;
      @ ensures \result != null;
      @ ensures (\forall int j; j >= 0 && j < \result.length; \result[j].start == n || \result[j].end == n || \result[j] == null);
      @*/

    /*@ public normal_behavior
      @ requires \invariant_for(n);
      @ assignable \nothing;
      @ ensures \result != null;
      @ ensures (\forall int j; j >= 0 && j < \result.length; \result[j].start.equals(n) || \result[j].end.equals(n) || \result[j] == null);
      @*/
    public /*@ nullable @*/ Edge[] getAllEdgesAt(Node n) {
        Edge[] returnval = new Edge[edges.length];
        int pos = 0;


        /* loop_invariant
          @ i >= 0 && i <= edges.length && pos >= 0 && pos <= i &&
          @   (\forall int j; j >= 0 && j < pos; returnval[j].start == n || returnval[j].end == n) &&
          @   (\forall int k; k >= pos && k < returnval.length; returnval[k] == null);
          @ assignable returnval[*];
          @ decreases edges.length - i;
          @*/

        /*@ loop_invariant
          @ i >= 0 && i <= edges.length && pos >= 0 && pos <= i &&
          @   (\forall int j; j >= 0 && j < pos; returnval[j] != null && (returnval[j].getStart().equals(n) || returnval[j].getEnd().equals(n))) &&
          @   (\forall int k; k >= pos && k < returnval.length; returnval[k] == null) &&
          @   (\forall int j; j >= 0 && j < pos; (\exists int m; m >= 0 && m < i; returnval[j] == edges[m]));
          @ assignable returnval[*];
          @ decreases edges.length - i;
          @*/
        for (int i = 0; i < edges.length; i++) {
            Edge tempEdge = edges[i];
            Node startNode = tempEdge.getStart();
            Node endNode = tempEdge.getEnd();

            if (startNode.equals(n) || endNode.equals(n)) {
                returnval[pos] = tempEdge;
                pos++;
            }

        }

        return returnval;
    }

    public static void main(String[] args) {

    }

}
