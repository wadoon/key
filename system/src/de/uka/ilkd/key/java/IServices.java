package de.uka.ilkd.key.java;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.proof.Counter;
import de.uka.ilkd.key.proof.NameRecorder;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.util.KeYExceptionHandler;

public interface IServices {

	public abstract KeYExceptionHandler getExceptionHandler();

	public abstract void setExceptionHandler(KeYExceptionHandler keh);

	/**
	 * Returns the TypeConverter associated with this Services object.
	 */
	public abstract TypeConverter getTypeConverter();

	public abstract NameRecorder getNameRecorder();

	public abstract void saveNameRecorder(Node n);

	public abstract void addNameProposal(Name proposal);

	public abstract SpecificationRepository getSpecificationRepository();

	/**
	 * Returns the VariableNamer associated with this Services object.
	 */
	public abstract VariableNamer getVariableNamer();

	/**
	 * creates a new services object containing a copy of the java info of
	 * this object and a new TypeConverter (shallow copy)
	 * @return the copy
	 */
	public abstract IServices copy();

	/**
	 * creates a new service object with the same ldt information 
	 * as the actual one
	 */
	public abstract IServices copyPreservesLDTInformation();

	public abstract IServices copyProofSpecific(Proof p_proof);

	/*
	 * returns an existing named counter, creates a new one otherwise
	 */
	public abstract Counter getCounter(String name);

	public abstract void setBackCounters(Node n);

	/**
	 * returns the namespaces for functions, predicates etc.
	 * @return the proof specific namespaces
	 */
	public abstract NamespaceSet getNamespaces();

	/**
	 * sets the namespaces of known predicates, functions, variables
	 * @param namespaces the NamespaceSet with the proof specific namespaces
	 */
	public abstract void setNamespaces(NamespaceSet namespaces);

	/**
	 * Returns the proof to which this object belongs, or null if it does not 
	 * belong to any proof.
	 */
	public abstract Proof getProof();
	
	public abstract IProgramInfo getProgramInfo();

	public abstract IProgramInfo getJavaInfo();

	public abstract TermBuilder getTermBuilder();


}