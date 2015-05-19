package org.key_project.starvoors.model;

public class StaRVOOrSExecutionPath {
   private final String pathCondition;
   
   private final boolean verified;
   
   private final boolean allPreconditionsFulfilled;
   
   private final boolean allNotNullChecksFulfilled;
    
   private final boolean allLoopInvariantsInitiallyFulfilled;
   
   private final boolean allLoopInvariantsPreserved;

   public StaRVOOrSExecutionPath(String pathCondition, 
                                 boolean verified,
                                 boolean allPreconditionsFulfilled,
                                 boolean allNotNullChecksFulfilled,
                                 boolean allLoopInvariantsInitiallyFulfilled,
                                 boolean allLoopInvariantsPreserved) {
      this.pathCondition = pathCondition;
      this.verified = verified;
      this.allPreconditionsFulfilled = allPreconditionsFulfilled;
      this.allNotNullChecksFulfilled = allNotNullChecksFulfilled;
      this.allLoopInvariantsInitiallyFulfilled = allLoopInvariantsInitiallyFulfilled;
      this.allLoopInvariantsPreserved = allLoopInvariantsPreserved;
   }

   public String getPathCondition() {
      return pathCondition;
   }

   public boolean isVerified() {
      return verified;
   }

   public boolean isAllPreconditionsFulfilled() {
      return allPreconditionsFulfilled;
   }

   public boolean isAllNotNullChecksFulfilled() {
      return allNotNullChecksFulfilled;
   }

   public boolean isAllLoopInvariantsInitiallyFulfilled() {
      return allLoopInvariantsInitiallyFulfilled;
   }

   public boolean isAllLoopInvariantsPreserved() {
      return allLoopInvariantsPreserved;
   }
}
