package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;

/**
 * Interface for all specification elements to be displayed
 * in proof management dialog.
 * @author bruns
 *
 */
public interface DisplayableSpecificationElement<T extends DisplayableSpecificationElement<?>> 
extends SpecificationElement {

    /**
     * For display (e.g., in ProofManagementDialog).
     * Optional operation.
     */
    public String getHTMLText(Services serv);

    public int id();

    public ProofOblInput createProofObl(InitConfig copyWithServices, T contract);
    
}
