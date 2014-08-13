package org.key_project.starvoors.model;

import java.util.LinkedList;
import java.util.List;

public class StaRVOOrSProof {
   private final List<StaRVOOrSExecutionPath> paths = new LinkedList<StaRVOOrSExecutionPath>();
   
   private final String contractId;

   private final String contractText;
   
   public StaRVOOrSProof(String contractId, String contractText) {
      this.contractId = contractId;
      this.contractText = contractText;
   }

   public void addPath(StaRVOOrSExecutionPath path) {
      if (path != null) {
         paths.add(path);
      }
   }
   
   public StaRVOOrSExecutionPath[] getPaths() {
      return paths.toArray(new StaRVOOrSExecutionPath[paths.size()]);
   }

   public String getContractId() {
      return contractId;
   }

   public String getContractText() {
      return contractText;
   }
}
