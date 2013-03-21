package de.uka.ilkd.keyabs.proof.mgt;

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
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.speclang.dl.InterfaceInvariant;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

public class ABSSpecificationRepository implements ISpecificationRepository {

    private HashMap<ProofOblInput,ImmutableSet<Proof>> proofs = new HashMap<ProofOblInput,ImmutableSet<Proof>>();
    private HashMap<KeYJavaType, ImmutableSet<InterfaceInvariant>> interfaceInvariants = new HashMap<>();
    private HashMap<String, ImmutableSet<ClassInvariant>> classInvariants = new HashMap<>();

    private final ABSServices services;
    
    public ABSSpecificationRepository(ABSServices absServices) {
        this.services = absServices;
    }


    public ImmutableSet<ClassInvariant> getClassInvariants(String className) {
        ImmutableSet<ClassInvariant> result = classInvariants.get(className);
        return result == null ? DefaultImmutableSet.<ClassInvariant>nil() : result;
    }

    public ImmutableSet<InterfaceInvariant> getInterfaceInvariants(KeYJavaType kjt) {
        ImmutableSet<InterfaceInvariant> result = interfaceInvariants.get(kjt);
        return result == null ? DefaultImmutableSet.<InterfaceInvariant>nil() : result;
    }

    @Override
    public ImmutableSet<ClassInvariant> getClassInvariants(KeYJavaType kjt) {
        return null;
    }

    @Override
    public ImmutableSet<Contract> getAllContracts() {
        return null;
    }

    @Override
    public ImmutableSet<Contract> getContracts(KeYJavaType kjt,
            IObserverFunction target) {
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
        ImmutableSet<ClassInvariant> invariants = classInvariants.get(inv.getClassName());
        if (invariants == null) {
            invariants = DefaultImmutableSet.<ClassInvariant>nil();
        }
        classInvariants.put(inv.getClassName(), invariants.add(inv));
    }

    @Override
    public void addClassInvariants(ImmutableSet<? extends ClassInvariant> toAdd) {
        if (toAdd != null) {
            for (ClassInvariant inv : toAdd) {
                addClassInvariant(inv);
            }
        }
    }

    public void addInterfaceInvariant(InterfaceInvariant inv) {
        ImmutableSet<InterfaceInvariant> invariants = interfaceInvariants.get(inv.getKJT());
        if (invariants == null) {
            invariants = DefaultImmutableSet.<InterfaceInvariant>nil();
        }

        interfaceInvariants.put(inv.getKJT(), invariants.add(inv));
    }

    public void addInterfaceInvariants(ImmutableSet<InterfaceInvariant> toAdd) {
        if (toAdd != null) {
            for (InterfaceInvariant inv : toAdd) {
                addInterfaceInvariant(inv);
            }
        }
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

	@Override
	public ProofOblInput getProofOblInput(Proof proof) {
		// TODO Auto-generated method stub
		return null;
	}

}
