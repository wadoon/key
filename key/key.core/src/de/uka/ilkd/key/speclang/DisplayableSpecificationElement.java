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
public interface DisplayableSpecificationElement extends SpecificationElement {

	/**
	 * For display (e.g., in ProofManagementDialog) in pretty HTML format.
	 * Optional operation.
	 */
	public String getHTMLText(Services serv);

	/**
     * Returns the contract in pretty plain text format.
     */
    public String getPlainText(Services services);

	public int id();

	/**
	 * Create a new PO from this specification element.
	 */
	public ProofOblInput createProofObl(InitConfig copyWithServices);
}