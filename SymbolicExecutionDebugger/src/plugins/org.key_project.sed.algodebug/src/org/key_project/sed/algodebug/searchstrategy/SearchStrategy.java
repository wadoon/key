package org.key_project.sed.algodebug.searchstrategy;

import org.key_project.sed.algodebug.model.MethodCall;

public class SearchStrategy {
   protected boolean searchCompletedButNoBugFound = false;
   protected boolean bugFound = false;
   protected MethodCall bug;

   public SearchStrategy(){

   }

   public boolean searchCompletedButNoBugFound() {
      return searchCompletedButNoBugFound;
   }

   public boolean bugFound() {
      return bugFound;
   }
   
   public MethodCall getBug() {
      return bug;
   }
}