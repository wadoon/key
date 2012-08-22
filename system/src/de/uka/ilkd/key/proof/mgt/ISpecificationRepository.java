package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.util.Pair;

public interface ISpecificationRepository {

    /**
     * Returns all known class invariants for the passed type.
     */
    public abstract ImmutableSet<ClassInvariant> getClassInvariants(
            KeYJavaType kjt);

    /**
     * Returns all registered contracts.
     */
    public abstract ImmutableSet<Contract> getAllContracts();

    /**
     * Returns all registered (atomic) contracts for the passed target.
     */
    public abstract ImmutableSet<Contract> getContracts(KeYJavaType kjt,
            IObserverFunction target);

    /**
     * Returns all registered (atomic) operation contracts for the passed 
     * operation.
     */
    public abstract ImmutableSet<FunctionalOperationContract> getOperationContracts(
            KeYJavaType kjt, IProgramMethod pm);

    /**
     * Returns all registered (atomic) operation contracts for the passed 
     * operation which refer to the passed modality.
     */
    public abstract ImmutableSet<FunctionalOperationContract> getOperationContracts(
            KeYJavaType kjt, IProgramMethod pm, Modality modality);

    /**
     * Returns the registered (atomic or combined) contract corresponding to the 
     * passed name, or null.
     */
    public abstract Contract getContractByName(String name);

    /**
     * Returns a set encompassing the passed contract and all its versions 
     * inherited to overriding methods.
     */
    public abstract ImmutableSet<Contract> getInheritedContracts(
            Contract contract);

    /**
     * Returns a set encompassing the passed contracts and all its versions 
     * inherited to overriding methods.
     */
    public abstract ImmutableSet<Contract> getInheritedContracts(
            ImmutableSet<Contract> contractSet);

    /**
     * Returns all functions for which contracts are registered in the passed
     * type.
     */
    public abstract ImmutableSet<IObserverFunction> getContractTargets(
            KeYJavaType kjt);

    /**
     * Registers the passed (atomic) contract, and inherits it to all
     * overriding methods.
     */
    public abstract void addContract(Contract contract);

    /** Registers the passed (atomic) contract without inheriting it. */
    public abstract void addContractNoInheritance(Contract contract);

    /**
     * Registers the passed contracts.
     */
    public abstract void addContracts(ImmutableSet<Contract> toAdd);

    /**
     * Registers the passed class invariant, and inherits it to all
     * subclasses if it is public or protected.
     */
    public abstract void addClassInvariant(ClassInvariant inv);

    /**
     * Registers the passed class invariants.
     */
    public abstract void addClassInvariants(ImmutableSet<ClassInvariant> toAdd);

    /**
     * Registers the passed class axiom.
     */
    public abstract void addClassAxiom(ClassAxiom ax);

    /**
     * Registers the passed class axioms.
     */
    public abstract void addClassAxioms(ImmutableSet<ClassAxiom> toAdd);

    /**
     * Returns all proofs registered for the passed PO (or stronger POs).
     */
    public abstract ImmutableSet<Proof> getProofs(ProofOblInput po);

    /**
     * Returns all proofs registered for the passed atomic contract, or for
     * combined contracts including the passed atomic contract
     */
    public abstract ImmutableSet<Proof> getProofs(Contract atomicContract);

    /**
     * Returns all proofs registered for the passed target and its overriding
     * targets.
     */
    public abstract ImmutableSet<Proof> getProofs(KeYJavaType kjt,
            IObserverFunction target);

    /**
     * Returns all proofs registered with this specification repository.
     */
    public abstract ImmutableSet<Proof> getAllProofs();

    /**
     * Returns the PO that the passed proof is about, or null.
     */
    public abstract ContractPO getPOForProof(Proof proof);

    /**
     * Registers the passed proof. 
     */
    public abstract void registerProof(ProofOblInput po, Proof proof);

    /**
     * Unregisters the passed proof.
     */
    public abstract void removeProof(Proof proof);
    
    public ProofOblInput getProofOblInput(Proof proof);

    public abstract Contract combineOperationContracts(
            ImmutableSet<FunctionalOperationContract> contracts);

    public abstract LoopInvariant getLoopInvariant(LoopStatement node);

    public abstract void setLoopInvariant(LoopInvariant newInv);

    public abstract ImmutableSet<Contract> splitContract(Contract contract);

    public abstract IObserverFunction unlimitObs(IObserverFunction target);

    public abstract IObserverFunction getTargetOfProof(Proof p);

    public abstract Pair<IObserverFunction, ImmutableSet<Taclet>> limitObs(
            IObserverFunction obs);

    public abstract void addSpecs(ImmutableSet<SpecificationElement> classSpecs);

    public abstract void createContractsFromInitiallyClauses();

}