package de.uka.ilkd.key.informationflow.po;

import org.key_project.common.core.logic.Named;

import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.proof.init.ProofOblInput;

public interface InfFlowPO extends ProofOblInput {

    public IFProofObligationVars getLeaveIFVars();

    public InfFlowProofSymbols getIFSymbols();

    public void addIFSymbol(JavaDLTerm t);

    public void addIFSymbol(Named n);

    public void addLabeledIFSymbol(JavaDLTerm t);

    public void addLabeledIFSymbol(Named n);

    public void unionLabeledIFSymbols(InfFlowProofSymbols symbols);
    
}
