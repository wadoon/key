package de.uka.ilkd.key.nui.printer;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.io.ProofSaver;

/**
 * Printer for TermInfo, copied from de.uka.ilkd.key.gui.nodeviews.SequentViewInputListener.
 * @author Victor Schuemmer
 */
public class TermInfoPrinter {
    public static String printTermInfo(Sequent sequent, PosInSequent pos) {
        String info = null;
        Term t;
        if (pos != null) {
            PosInOccurrence occ = pos.getPosInOccurrence();
            if (occ != null) {
                t = occ.subTerm();
                String tOpClassString = t.op().getClass().toString();
                String operator = tOpClassString
                        .substring(tOpClassString.lastIndexOf('.') + 1);
                // The hash code is displayed here since sometimes terms with
                // equal string representation are still different.
                info = operator + ", Sort: " + t.sort() + ", Hash: "
                        + t.hashCode();

                info += ProofSaver.posInOccurrence2Proof(sequent, occ);
            }
        }
        return info;
    }
}
