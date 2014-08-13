package org.key_project.starvoors.model;

public class StaRVOOrSExecutionPath {
   private final String pathCondition;
   
   private final boolean verified;

   public StaRVOOrSExecutionPath(String pathCondition, boolean verified) {
      this.pathCondition = pathCondition;
      this.verified = verified;
   }

   public String getPathCondition() {
      return pathCondition;
   }

   public boolean isVerified() {
      return verified;
   }
}
