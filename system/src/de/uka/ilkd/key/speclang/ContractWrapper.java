package de.uka.ilkd.key.speclang;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContractImpl;

/**
 * Wrapper for extracting raw preconditions and postconditions from
 * {@link FunctionalOperationContract} instances.
 * 
 * @author christopher
 */
public class ContractWrapper
        extends FunctionalOperationContractImpl {

    public ContractWrapper(FunctionalOperationContractImpl contract) {
        super(contract.baseName,
                contract.name,
                contract.kjt, 
                contract.pm, 
                contract.specifiedIn,
                contract.modality, 
                contract.originalPres, 
                contract.originalMby,
                contract.originalPosts,
                contract.originalAxioms,
                contract.originalMods,
                contract.originalDeps,
                contract.hasRealModifiesClause,
                contract.originalSelfVar,
                contract.originalParamVars,
                contract.originalExcVar, 
                contract.originalExcVar,
                contract.originalAtPreVars,
                contract.globalDefs,
                contract.id,
                contract.toBeSaved,
                contract.transaction,
                contract.services,
                contract.escapeHatches
                );
    }
    

    public List<Term> getPostconditions() {

        List<Term> postConditions = new LinkedList<Term>();
        for (Term term : originalPosts.values()) {
            postConditions.add(term);
        }

        return postConditions;
    }

    public List<Term> getPreconditions() {

        List<Term> postConditions = new LinkedList<Term>();
        for (Term term : originalPres.values()) {
            postConditions.add(term);
        }

        return postConditions;
    }

    public List<IProgramVariable> getParameters() {

        List<IProgramVariable> parameters = new LinkedList<IProgramVariable>();
        for (IProgramVariable term : originalParamVars) {
            parameters.add(term);
        }

        return parameters;
    }
    
    //added by Huy, serves KEG
    public List<Term> getEscapeHatchTerms(){
       List<Term> escapeHatcheTerms = new LinkedList<Term>();
       if(escapeHatches !=null){
          for (Term term : escapeHatches.values()) {
             escapeHatcheTerms.add(term);
          }
       }   
       return escapeHatcheTerms;
    }
    
    public boolean hasNotNullEscapeHatchTerms(){
       if(getEscapeHatchTerms().get(0)!=null)
          return true;
       return false;
    }
}
