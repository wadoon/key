package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.Services;

/**
 * Interface for all specification elements to be displayed
 * in proof management dialog.
 * @author bruns
 *
 */
public interface DisplayableSpecificationElement extends SpecificationElement {

    /**
     * For display (e.g., in ProofManagementDialog).
     * Optional operation.
     */
    public String getHTMLText(Services serv);

    public int id();
    
}
