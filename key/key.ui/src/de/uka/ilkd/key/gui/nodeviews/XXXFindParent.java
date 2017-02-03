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
        Pair<Node, Integer> parent = findParentWithSCI(formula, antec, node);

        Node parentNode = parent.first;
        int siblingNumber = parent.second;
        TrackNode nodeToAdd = null;

        //if the applied rule, that resulted in adding the formula was allLeft, we have to retrieve the quantified formula
        if (parentNode.getAppliedRuleApp().rule().displayName().equals("allLeft")) {
            nodeToAdd = new TrackNode(parentNode);
            RuleApp rap = parentNode.getAppliedRuleApp();
            nodeToAdd.addPositionToHighlight(rap.posInOccurrence());
            nodeToAdd.addParentFormula(rap.posInOccurrence().sequentFormula());
            return nodeToAdd;

        }else {

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
                List<Pair<SequentFormula, PosInOccurrence>> parentF= findParentFormula(sci, formula);
                for (Pair<SequentFormula, PosInOccurrence> sequentFormulaPosInOccurrencePair : parentF) {
                    nodeToAdd.addPositionToHighlight(sequentFormulaPosInOccurrencePair.second);
                    nodeToAdd.addParentFormula(sequentFormulaPosInOccurrencePair.first);
                }
            }
            return nodeToAdd;
        }


    }

    /**
     * Find list of parentformulas, that need to be tracked in the following for one specific node
     * @param sci
     * @param formula
     * @return
     */
    private static List<Pair<SequentFormula, PosInOccurrence>> findParentFormula(SequentChangeInfo sci, SequentFormula formula) {
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
        1. Removed Formula either in succ or antec and added formula in succ or antec:
        a & b ==> ~~> a, b ==> added (a,b), removed (a&b)
        Parent(removed): (a&b), child(ren)(added): a, b
        2. Added Formula without a delete:
        Cut: a = b ==> added(a= b) Parent: none
        3. Child is a result of a substitution in another formula
        a=b, a= c ~~> c=b, a=c Modification of a posInOcc
        */



        //if formula is in added list
        if(addedAntec.size() > 0 || addedSucc.size() > 0) {
            //search in deleted list for parents
            if (addedAntec.contains(formula) || addedSucc.contains(formula)) {
                if (delAntec.size() > 0) {
                    Iterator<SequentFormula> iter = delAntec.iterator();
                    while (iter.hasNext()) {
                        SequentFormula curr = iter.next();
                        PosInOccurrence pio = new PosInOccurrence(curr, PosInTerm.getTopLevel(), true);
                        pas.add(new Pair<>(curr, pio));

                        parents.add(curr);
                        //   System.out.println("ParentAntec: "+curr);
                        //   System.out.println("Child: "+formula);

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
                            //System.out.println("Child: "+formula);
                        }

                    }
                }
                //formula was added and resulted from a parent formula (allLeft)
                if(parents.size() == 0){
                    if(addedAntec.contains(formula)){
                        parents.add(formula);
                        pas.add(new Pair<>(formula, new PosInOccurrence(formula, PosInTerm.getTopLevel(), true)));
                    }else{
                        if(addedSucc.contains(formula)) {
                            parents.add(formula);
                            pas.add(new Pair<>(formula, new PosInOccurrence(formula, PosInTerm.getTopLevel(), false)));
                        }
                    }


                }
            }

        }else{
            //formula was not added or deleted but modified e.g. applyEq
            Iterator<FormulaChangeInfo> iter = antecModif.iterator();
            while(iter.hasNext()){
                FormulaChangeInfo fci = iter.next();
                if(fci.getNewFormula().equals(formula)){
                    parents.add(fci.getOriginalFormula());
                    pas.add(new Pair<>(fci.getOriginalFormula(), fci.getPositionOfModification()));

                    //System.out.println("ParentAntec :"+fci.getOriginalFormula());
                    //System.out.println("Child :"+formula);
                }
            }
            Iterator<FormulaChangeInfo> iter2 = succModif.iterator();
            while(iter2.hasNext()){
                FormulaChangeInfo fci = iter2.next();
                if(fci.getNewFormula().equals(formula)){
                    parents.add(fci.getOriginalFormula());
                    pas.add(new Pair<>(fci.getOriginalFormula(), fci.getPositionOfModification()));

                   // System.out.println("ParentSucc :"+fci.getOriginalFormula());
                    //System.out.println("Child :"+formula);
                }
            }

        }

        if(parents.size() == 0 && (addedAntec.contains(formula) || addedSucc.contains(formula))){



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
