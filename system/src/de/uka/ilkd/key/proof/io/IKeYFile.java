package de.uka.ilkd.key.proof.io;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;

public interface IKeYFile<S extends IServices, IC extends InitConfig<S, IC>> extends EnvInput<S, IC> {

    /** reads the sorts declaration of the .key file only, 
     * modifying the sort namespace
     * of the initial configuration 
     */
    public abstract void readSorts() throws ProofInputException;

    /** reads the functions and predicates declared in the .key file only, 
     * modifying the function namespaces of the respective taclet options. 
     */
    public abstract void readFuncAndPred() throws ProofInputException;

    /** reads the rules and problems declared in the .key file only, 
     * modifying the set of rules 
     * of the initial configuration 
     */
    public abstract void readRulesAndProblem() throws ProofInputException;

    public abstract void close();

    public abstract String chooseContract();

	public abstract String getProofObligation();

}