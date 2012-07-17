package de.uka.ilkd.key.java;

import java.util.HashMap;

import de.uka.ilkd.key.logic.InnerVariableNamer;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.proof.Counter;
import de.uka.ilkd.key.proof.NameRecorder;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.KeYExceptionHandler;

public abstract class AbstractServices implements IServices {

	/**
	 * the proof
	 */
	protected Proof proof;

	public abstract IServices copyPreservesLDTInformation();

	public abstract IServices copy();

	/**
	 * proof specific namespaces (functions, predicates, sorts, variables)
	 */
	protected NamespaceSet namespaces = new NamespaceSet();
	/** used to convert types, expressions and so on to logic elements
	 * (in special into to terms or formulas)
	 */
	protected TypeConverter typeconverter;
	/**
	 * variable namer for inner renaming
	 */
	private final VariableNamer innerVarNamer = new InnerVariableNamer(this);
	/**
	 * the exception-handler
	 */
	protected KeYExceptionHandler exceptionHandler;
	/**
	 * map of names to counters
	 */
	private HashMap<String, Counter> counters = new HashMap<String, Counter>();
	protected NameRecorder nameRecorder;

	public AbstractServices() {
		super();
	}

	@Override
	public KeYExceptionHandler getExceptionHandler() {
	return exceptionHandler;
	}

	@Override
	public void setExceptionHandler(KeYExceptionHandler keh) {
	exceptionHandler = keh;
	}

	@Override
	public NameRecorder getNameRecorder() {
	    return nameRecorder;
	}

	@Override
	public VariableNamer getVariableNamer() {
	    return innerVarNamer;
	}

	@Override
	public abstract IServices copyProofSpecific(Proof p_proof);

	@Override
	public Counter getCounter(String name) {
	    Counter c = counters.get(name);
	    if (c != null) return c;
	    c = new Counter(name);
	    counters.put(name, c);
	    return c;
	}

	@Override
	public void setBackCounters(Node n) {        
	    for (final Counter c : counters.values()) {
	        c.undo(n);
	    }
	}

	@Override
	public NamespaceSet getNamespaces() {
	    return namespaces;
	}

	@Override
	public void setNamespaces(NamespaceSet namespaces) {
	    this.namespaces = namespaces;
	}

	@Override
	public Proof getProof() {
	return proof;
	}

}