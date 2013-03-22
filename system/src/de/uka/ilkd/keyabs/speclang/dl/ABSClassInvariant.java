package de.uka.ilkd.keyabs.speclang.dl;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ParsableVariable;

/**
 * Created with IntelliJ IDEA.
 * User: bubel
 * Date: 20.03.13
 * Time: 23:54
 * To change this template use File | Settings | File Templates.
 */
public interface ABSClassInvariant extends de.uka.ilkd.key.speclang.ClassInvariant {

    /**
     * Returns the invariant formula without implicit all-quantification over
     * the receiver object.
     */
    Term getInv(ParsableVariable historyVar, ParsableVariable heapVar,
                ParsableVariable selfVar, IServices services);

}
