package org.key_project.starvoors.model;

import java.util.LinkedList;
import java.util.List;

public class StaRVOOrSResult {
   private final List<StaRVOOrSProof> proofs = new LinkedList<StaRVOOrSProof>();
   
   public void addProof(StaRVOOrSProof proof) {
      if (proof != null) {
         proofs.add(proof);
      }
   }
   
   public StaRVOOrSProof[] getProofs() {
      return proofs.toArray(new StaRVOOrSProof[proofs.size()]);
   }
}
