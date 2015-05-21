package org.key_project.starvoors.model;

public class StaRVOOrSMethodContractApplication extends AbstractStaRVOOrSApplication{
   private final String method;
   
   private final String contract;

   public StaRVOOrSMethodContractApplication(String file, int startLine, int startColumn, int endLine, int endColumn, String method, String contract) {
      super(file, startLine, startColumn, endLine, endColumn);
      this.method = method;
      this.contract = contract;
   }

   public String getMethod() {
      return method;
   }

   public String getContract() {
      return contract;
   }
}
