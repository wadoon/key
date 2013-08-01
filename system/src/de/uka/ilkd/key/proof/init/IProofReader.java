package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.proof.io.IProofFileParser;

public interface IProofReader {

	/** 
	 * Reads a saved proof of a .key file.
	 */
	public abstract void readProof(IProofFileParser prl)
			throws ProofInputException;

	public abstract int getNumberOfChars();

}