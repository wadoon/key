package de.uka.ilkd.key.gui.nodeviews;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableList;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

public class XXXFindParent {

    public static List<TrackNode> trackTransitive(SequentFormula initChild, PosInOccurrence pio, boolean antec, Node initNode){
        LinkedList<TrackNode> totrack = new LinkedList<>();

        //add initial child to tracklist
        TrackNode initial = new TrackNode(initNode);
        initial.addParentFormula(initChild);
        initial.addPositionToHighlight(pio);
        totrack.add(initial);
        List<Pair<SequentFormula, Node>> formulas = new LinkedList<>();
        formulas.add(new Pair(initChild, initNode));

        while(formulas.size() >0){

            Pair<SequentFormula, Node> next = formulas.remove(0);
            if(next == null){
                break;
            }
            boolean isAntec = next.second.sequent().antecedent().contains(next.first);
            TrackNode tn = findParentTrackNode(next.first, isAntec, next.second);
            totrack.add(tn);
            //add contents of tn to formulas
            List<SequentFormula> forms = tn.getParents();
            for (SequentFormula form : forms) {
                formulas.add(new Pair(form, tn.getNode()));
            }
        }
        return totrack;

    }



    public static TrackNode findParentTrackNode(SequentFormula formula, boolean antec, Node node){

        //finde Elternknoten
        SequentChangeInfo sci = null;
        //Knoten hat eine Aenderung an der Top-level SequentFormula
        Pair<Node, Integer> parent = findParentWithSCI(formula, antec, node);

        Node parentNode = parent.first;
        int siblingNumber = parent.second;
        TrackNode nodeToAdd = null;

            if (parentNode.childrenCount() == 1) {

                sci = parentNode.child(0).getNodeInfo().getSequentChangeInfo();
            } else {
                //if parent is a branching node
                Iterator<Node> it = parentNode.childrenIterator();
                while (it.hasNext()) {
                    Node child = it.next();
                    if (child.serialNr() == siblingNumber) {
                        sci = child.getNodeInfo().getSequentChangeInfo();
                        break;
                    }
                }
            }

            if (sci != null) {
                nodeToAdd = new TrackNode(parentNode);
                RuleApp rap = parentNode.getAppliedRuleApp();
                List<Pair<SequentFormula, PosInOccurrence>> parentF = findParentFormula(sci, formula, rap);
                for (Pair<SequentFormula, PosInOccurrence> sequentFormulaPosInOccurrencePair : parentF) {
                    nodeToAdd.addPositionToHighlight(sequentFormulaPosInOccurrencePair.second);
                    nodeToAdd.addParentFormula(sequentFormulaPosInOccurrencePair.first);
                }
            }
            return nodeToAdd;
//        }


    }

    /**
     * Find list of parentformulas, that need to be tracked in the following for one specific node
     * @param sci
     * @param child
     * @return
     */
    private static List<Pair<SequentFormula, PosInOccurrence>> findParentFormula(SequentChangeInfo sci, SequentFormula child, RuleApp rap) {
        List<SequentFormula> parents = new LinkedList<>();
        List<Pair<SequentFormula, PosInOccurrence>> pas = new LinkedList<>();

        SemisequentChangeInfo antec = sci.getSemisequentChangeInfo(true);
        SemisequentChangeInfo succ = sci.getSemisequentChangeInfo(false);


        //Get deleted, added lists and modfied lists
        ImmutableList<SequentFormula> addedAntec = antec.addedFormulas();
        ImmutableList<SequentFormula> addedSucc = succ.addedFormulas();
        ImmutableList<SequentFormula> delAntec = antec.removedFormulas();
        ImmutableList<SequentFormula> delSucc = succ.removedFormulas();

        ImmutableList<FormulaChangeInfo> antecModif = antec.modifiedFormulas();
        ImmutableList<FormulaChangeInfo> succModif = succ.modifiedFormulas();

        /*Cases:
        1. Removed Formula either in succ or antec and added child in succ or antec:
        a & b ==> ~~> a, b ==> added (a,b), removed (a&b)
        Parent(removed): (a&b), child(ren)(added): a, b
        2. Added Formula without a delete:
        Cut: a = b ==> added(a= b) Parent: none
        3. Child is a result of a substitution in another child
        a=b, a= c ~~> c=b, a=c Modification of a posInOcc
        */



        //if child is in added list
        if(addedAntec.size() > 0 || addedSucc.size() > 0) {
            //search in deleted list for parents
            if (addedAntec.contains(child) || addedSucc.contains(child)) {
                if (delAntec.size() > 0) {
                    Iterator<SequentFormula> iter = delAntec.iterator();
                    while (iter.hasNext()) {
                        SequentFormula curr = iter.next();
                        PosInOccurrence pio = new PosInOccurrence(curr, PosInTerm.getTopLevel(), true);
                        pas.add(new Pair<>(curr, pio));

                        parents.add(curr);
                        //   System.out.println("ParentAntec: "+curr);
                        //   System.out.println("Child: "+child);

                    }
                } else {
                    if (delSucc.size() > 0) {
                        Iterator<SequentFormula> iter = delSucc.iterator();
                        while (iter.hasNext()) {
                            SequentFormula curr = iter.next();
                            PosInOccurrence pio = new PosInOccurrence(curr, PosInTerm.getTopLevel(), false);
                            pas.add(new Pair<>(curr, pio));

                            parents.add(curr);
                            //System.out.println("ParentSucc: "+curr);
                            //System.out.println("Child: "+child);
                        }

                    }
                }

                //if child was added and did not directly resulted from changing its parent, the parent has to be added from
                // RuleApp
                if(parents.size() == 0){
                    PosInOccurrence ruleApp = rap.posInOccurrence();
                    SequentFormula parent = ruleApp.sequentFormula();

                    if(addedAntec.contains(child)){
//                        parents.add(child);
//                        pas.add(new Pair<>(child, new PosInOccurrence(child, PosInTerm.getTopLevel(), true)));
                        parents.add(parent);
                        pas.add(new Pair(parent, ruleApp));

                    }else{
                        if(addedSucc.contains(child)) {
                            //parents.add(child);
                            //pas.add(new Pair<>(child, new PosInOccurrence(child, PosInTerm.getTopLevel(), false)));
                            parents.add(parent);
                            pas.add(new Pair(parent, ruleApp));
                        }
                    }


                }
            }

        }else{
            //child was not added or deleted but modified e.g. applyEq
            Iterator<FormulaChangeInfo> iter = antecModif.iterator();
            while(iter.hasNext()){
                FormulaChangeInfo fci = iter.next();
                if(fci.getNewFormula().equals(child)){
                    parents.add(fci.getOriginalFormula());
                    pas.add(new Pair<>(fci.getOriginalFormula(), fci.getPositionOfModification()));

                    //System.out.println("ParentAntec :"+fci.getOriginalFormula());
                    //System.out.println("Child :"+child);
                }
            }
            Iterator<FormulaChangeInfo> iter2 = succModif.iterator();
            while(iter2.hasNext()){
                FormulaChangeInfo fci = iter2.next();
                if(fci.getNewFormula().equals(child)){
                    parents.add(fci.getOriginalFormula());
                    pas.add(new Pair<>(fci.getOriginalFormula(), fci.getPositionOfModification()));

                   // System.out.println("ParentSucc :"+fci.getOriginalFormula());
                    //System.out.println("Child :"+child);
                }
            }

        }

        if(parents.size() == 0 && (addedAntec.contains(child) || addedSucc.contains(child))){



        }

        return pas;
    }


    /**
     * Method finding the parent node and the siblingNr that contains the corresponding SequentChangeInfo
     * @param formula
     * @param antec
     * @param node
     * @return Pair of Node and the child's number, that contaisn the SequentChangeInfo acc. to formula
     */
    public static Pair<Node, Integer> findParentWithSCI(SequentFormula formula, boolean antec, Node node){
        Node lastNode = node;
        int s = lastNode.serialNr();
        node = node.parent();


        while(node != null) {

            Sequent sequent = node.sequent();

            Semisequent semi;
            if(antec) {
                semi = sequent.antecedent();
            } else {
                semi = sequent.succedent();
            }

            if(!semi.contains(formula)) {
                return new Pair(node, s);
            }

            lastNode = node;
            s = node.serialNr();
            node = node.parent();


        }

        return new Pair(lastNode, s);
    }

    public static Node findParent(SequentFormula formula, boolean antec, Node node) {

        Node lastNode = node;
        node = node.parent();


        while(node != null) {
            Sequent sequent = node.sequent();

            Semisequent semi;
            if(antec) {
                semi = sequent.antecedent();
            } else {
                semi = sequent.succedent();
            }

            if(!semi.contains(formula)) {
                return node;
            }

            lastNode = node;

            node = node.parent();

        }

        return lastNode;
    }

}
