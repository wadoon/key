package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ParsableVariable;

/**
 *
 */
public interface ClassInvariant extends SpecificationElement {
    /**
     * Returns the invariant formula without implicit all-quantification over
     * the receiver object.
     */
    Term getInv(ParsableVariable selfVar, IServices services);

    /**
     * Returns the invariant formula without implicit all-quantification over
     * the receiver object.
     */
    Term getOriginalInv();

    /**
     * returns the name of the class to which the invariant belongs
     */
    String getClassName();
}
