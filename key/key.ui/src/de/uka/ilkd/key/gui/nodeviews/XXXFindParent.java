package de.uka.ilkd.key.gui.nodeviews;

import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.Node;

public class XXXFindParent {

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
