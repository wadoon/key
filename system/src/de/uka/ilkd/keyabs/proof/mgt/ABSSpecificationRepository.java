package de.uka.ilkd.keyabs.proof.mgt;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.ISpecificationRepository;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.SpecificationElement;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.keyabs.abs.ABSServices;

public class ABSSpecificationRepository implements ISpecificationRepository {

    private HashMap<ProofOblInput,ImmutableSet<Proof>> proofs = new HashMap<ProofOblInput,ImmutableSet<Proof>>();
    private final ABSServices services;
    
    public ABSSpecificationRepository(ABSServices absServices) {
        this.services = absServices;
    }

    @Override
    public ImmutableSet<ClassInvariant> getClassInvariants(KeYJavaType kjt) {
        return null;
    }

    @Override
    public ImmutableSet<Contract> getAllContracts() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ImmutableSet<Contract> getContracts(KeYJavaType kjt,
            IObserverFunction target) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ImmutableSet<FunctionalOperationContract> getOperationContracts(
            KeYJavaType kjt, IProgramMethod pm) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ImmutableSet<FunctionalOperationContract> getOperationContracts(
            KeYJavaType kjt, IProgramMethod pm, Modality modality) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Contract getContractByName(String name) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ImmutableSet<Contract> getInheritedContracts(Contract contract) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ImmutableSet<Contract> getInheritedContracts(
            ImmutableSet<Contract> contractSet) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ImmutableSet<IObserverFunction> getContractTargets(KeYJavaType kjt) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public void addContract(Contract contract) {
        // TODO Auto-generated method stub

    }

    @Override
    public void addContractNoInheritance(Contract contract) {
        // TODO Auto-generated method stub

    }

    @Override
    public void addContracts(ImmutableSet<Contract> toAdd) {
        // TODO Auto-generated method stub

    }

    @Override
    public void addClassInvariant(ClassInvariant inv) {
        // TODO Auto-generated method stub

    }

    @Override
    public void addClassInvariants(ImmutableSet<ClassInvariant> toAdd) {
        // TODO Auto-generated method stub

    }

    @Override
    public void addClassAxiom(ClassAxiom ax) {
        // TODO Auto-generated method stub

    }

    @Override
    public void addClassAxioms(ImmutableSet<ClassAxiom> toAdd) {
        // TODO Auto-generated method stub

    }

    @Override
    public ImmutableSet<Proof> getProofs(ProofOblInput po) {
        ImmutableSet<Proof> result = DefaultImmutableSet.<Proof>nil();
        for(Map.Entry<ProofOblInput,ImmutableSet<Proof>> entry 
                : proofs.entrySet()) {
            ProofOblInput mapPO = entry.getKey();
            ImmutableSet<Proof> sop = entry.getValue();
            if(mapPO.implies(po)) {
                result = result.union(sop);
            }
        }
        return result;
    }

    @Override
    public ImmutableSet<Proof> getProofs(Contract atomicContract) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ImmutableSet<Proof> getProofs(KeYJavaType kjt,
            IObserverFunction target) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ImmutableSet<Proof> getAllProofs() {
        ImmutableSet<Proof> result = DefaultImmutableSet.<Proof>nil();
        Collection<ImmutableSet<Proof>> proofSets = proofs.values();
        for(ImmutableSet<Proof> proofSet : proofSets) {
            result = result.union(proofSet);
        }
        return result;
    }

    @Override
    public ContractPO getPOForProof(Proof proof) {
        for(Map.Entry<ProofOblInput,ImmutableSet<Proof>> entry 
                : proofs.entrySet()) {
            ProofOblInput po = entry.getKey();
            ImmutableSet<Proof> sop = entry.getValue();
            if(sop.contains(proof) && po instanceof ContractPO) {
                return (ContractPO)po;
            }
        }
        return null;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.mgt.ISpecificationRepository#registerProof(de.uka.ilkd.key.proof.init.ProofOblInput, de.uka.ilkd.key.proof.Proof)
     */
    @Override
    public void registerProof(ProofOblInput po, Proof proof) {
        proofs.put(po, getProofs(po).add(proof));
    }    
    
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.mgt.ISpecificationRepository#removeProof(de.uka.ilkd.key.proof.Proof)
     */
    @Override
    public void removeProof(Proof proof) {
        for(Map.Entry<ProofOblInput,ImmutableSet<Proof>> entry 
                : proofs.entrySet()) {
            ImmutableSet<Proof> sop = entry.getValue();
            if(sop.contains(proof)) {
                sop = sop.remove(proof);
                if(sop.size()==0){
                    proofs.remove(entry.getKey());
                }else{
                    proofs.put(entry.getKey(), sop);
                }
                return;
            }
        }
    }

    @Override
    public Contract combineOperationContracts(
            ImmutableSet<FunctionalOperationContract> contracts) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public LoopInvariant getLoopInvariant(LoopStatement node) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public void setLoopInvariant(LoopInvariant newInv) {
        // TODO Auto-generated method stub
        
    }

    @Override
    public ImmutableSet<Contract> splitContract(Contract contract) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public IObserverFunction unlimitObs(IObserverFunction target) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public IObserverFunction getTargetOfProof(Proof p) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Pair<IObserverFunction, ImmutableSet<Taclet>> limitObs(
            IObserverFunction obs) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public void addSpecs(ImmutableSet<SpecificationElement> classSpecs) {
        // TODO Auto-generated method stub
        
    }

    @Override
    public void createContractsFromInitiallyClauses() {
        // TODO Auto-generated method stub
        
    }

}
