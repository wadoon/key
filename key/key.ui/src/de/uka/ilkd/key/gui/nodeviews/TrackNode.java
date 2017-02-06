package de.uka.ilkd.key.gui.nodeviews;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.Pair;

import java.util.ArrayList;
import java.util.List;

/**
 * Object encapsulating the information for a node to track (for History View)
 * Created by sarah on 2/3/17.
 */
public class TrackNode {


    public Node getNode() {
        return node;
    }

    public void setNode(Node node) {
        this.node = node;
    }


    public void addParentFormula(SequentFormula form){
        this.parents.add(form);
    }

    public List<SequentFormula> getParents(){
        return this.parents;
    }

    public void addPositionToHighlight(PosInOccurrence pio){
        this.positionsToHighlight.add(pio);

    }

    public List<Pair<SequentFormula, PosInOccurrence>> getHighlightMap() {
        return highlightMap;
    }

    public void setHighlightMap(List<Pair<SequentFormula, PosInOccurrence>> highlightMap) {
        this.highlightMap = highlightMap;
    }

    private List<Pair<SequentFormula, PosInOccurrence>> highlightMap;

    public List<PosInOccurrence> getPositionsToHighlight(){
        return this.positionsToHighlight;
    }

    public Node node;
    public List<SequentFormula> parents;
    public List<PosInOccurrence> positionsToHighlight;

    public TrackNode(Node node, List<SequentFormula> formula, List<PosInOccurrence> pio){
        this.node = node;
        this.parents = formula;
        this.positionsToHighlight = pio;
        this.highlightMap = new ArrayList<>();
        this.highlightMap.add(new Pair(formula, pio));

    }

    public TrackNode(Node node){
        this.node = node;
        this.positionsToHighlight = new ArrayList<>();
        this.parents = new ArrayList<>();
        this.highlightMap = new ArrayList<>();
    }

    public String toString(){
        String s=  "Parent NodeNr: "+this.node.serialNr()+"\n";
        for (SequentFormula parent : parents) {
            s+= "Parent formula: "+parent.toString()+"\n";
        }
        for (PosInOccurrence pos : positionsToHighlight) {
            s+= "Position to Highlight: "+pos.toString();
        }


        return s;
    }

}
