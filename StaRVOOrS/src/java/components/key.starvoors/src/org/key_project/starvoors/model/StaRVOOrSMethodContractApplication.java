package org.key_project.starvoors.model;

public class StaRVOOrSMethodContractApplication extends AbstractStaRVOOrSApplication{
   private final String type;
   
   private final String method;
   
   private final String contract;

   public StaRVOOrSMethodContractApplication(String file, int startLine, int startColumn, int endLine, int endColumn, String type, String method, String contract) {
      super(file, startLine, startColumn, endLine, endColumn);
      this.type = type;
      this.method = method;
      this.contract = contract;
   }

   public String getType() {
      return type;
   }

   public String getMethod() {
      return method;
   }

   public String getContract() {
      return contract;
   }
}
