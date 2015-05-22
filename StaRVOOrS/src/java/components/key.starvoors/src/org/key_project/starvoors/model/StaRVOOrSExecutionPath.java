package org.key_project.starvoors.model;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination.TerminationKind;

public class StaRVOOrSExecutionPath {
   private final String pathCondition;
   
   private final boolean verified;
   
   private final String newPrecondition;
   
   private final List<StaRVOOrSMethodContractApplication> notFulfilledPreconditions = new LinkedList<StaRVOOrSMethodContractApplication>();
   
   private final List<StaRVOOrSMethodContractApplication> notFulfilledNullChecks = new LinkedList<StaRVOOrSMethodContractApplication>();
    
   private final List<StaRVOOrSLoopInvariantApplication> notInitiallyValidLoopInvariants = new LinkedList<StaRVOOrSLoopInvariantApplication>();
   
   private final List<StaRVOOrSLoopInvariantApplication> notPreservedLoopInvariants = new LinkedList<StaRVOOrSLoopInvariantApplication>();
   
   private final TerminationKind terminationKind;

   public StaRVOOrSExecutionPath(String pathCondition, 
                                 boolean verified,
                                 List<StaRVOOrSMethodContractApplication> notFulfilledPreconditions,
                                 List<StaRVOOrSMethodContractApplication> notFulfilledNullChecks,
                                 List<StaRVOOrSLoopInvariantApplication> notInitiallyValidLoopInvariants,
                                 List<StaRVOOrSLoopInvariantApplication> notPreservedLoopInvariants,
                                 TerminationKind terminationKind,
                                 String newPrecondition) {
      this.pathCondition = pathCondition;
      this.verified = verified;
      if (notFulfilledPreconditions != null) {
         this.notFulfilledPreconditions.addAll(notFulfilledPreconditions);
      }
      if (notFulfilledNullChecks != null) {
         this.notFulfilledNullChecks.addAll(notFulfilledNullChecks);
      }
      if (notInitiallyValidLoopInvariants != null) {
         this.notInitiallyValidLoopInvariants.addAll(notInitiallyValidLoopInvariants);
      }
      if (notPreservedLoopInvariants != null) {
         this.notPreservedLoopInvariants.addAll(notPreservedLoopInvariants);
      }
      this.terminationKind = terminationKind;
      this.newPrecondition = newPrecondition;
   }

   public String getPathCondition() {
      return pathCondition;
   }

   public boolean isVerified() {
      return verified;
   }

   public boolean isAllPreconditionsFulfilled() {
      return notFulfilledPreconditions.isEmpty();
   }

   public boolean isAllNotNullChecksFulfilled() {
      return notFulfilledNullChecks.isEmpty();
   }

   public boolean isAllLoopInvariantsInitiallyFulfilled() {
      return notInitiallyValidLoopInvariants.isEmpty();
   }

   public boolean isAllLoopInvariantsPreserved() {
      return notPreservedLoopInvariants.isEmpty();
   }

   public StaRVOOrSMethodContractApplication[] getNotFulfilledPreconditions() {
      return notFulfilledPreconditions.toArray(new StaRVOOrSMethodContractApplication[notFulfilledPreconditions.size()]);
   }

   public StaRVOOrSMethodContractApplication[] getNotFulfilledNullChecks() {
      return notFulfilledNullChecks.toArray(new StaRVOOrSMethodContractApplication[notFulfilledNullChecks.size()]);
   }

   public StaRVOOrSLoopInvariantApplication[] getNotInitiallyValidLoopInvariants() {
      return notInitiallyValidLoopInvariants.toArray(new StaRVOOrSLoopInvariantApplication[notInitiallyValidLoopInvariants.size()]);
   }

   public StaRVOOrSLoopInvariantApplication[] getNotPreservedLoopInvariants() {
      return notPreservedLoopInvariants.toArray(new StaRVOOrSLoopInvariantApplication[notPreservedLoopInvariants.size()]);
   }

   public TerminationKind getTerminationKind() {
      return terminationKind;
   }

   public void addNotFulfilledPrecondition(StaRVOOrSMethodContractApplication application) {
      if (application != null) {
         notFulfilledPreconditions.add(application);
      }
   }

   public void addNotFulfilledNullCheck(StaRVOOrSMethodContractApplication application) {
      if (application != null) {
         notFulfilledNullChecks.add(application);
      }
   }

   public void addNotInitiallyValidLoopInvariant(StaRVOOrSLoopInvariantApplication application) {
      if (application != null) {
         notInitiallyValidLoopInvariants.add(application);
      }
   }

   public void addNotPreservedLoopInvariant(StaRVOOrSLoopInvariantApplication application) {
      if (application != null) {
         notPreservedLoopInvariants.add(application);
      }
   }

   public String getNewPrecondition() {
      return newPrecondition;
   }
}
