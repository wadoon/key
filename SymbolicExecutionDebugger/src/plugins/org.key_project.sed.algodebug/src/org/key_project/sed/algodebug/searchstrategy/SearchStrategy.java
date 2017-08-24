package org.key_project.sed.algodebug.searchstrategy;

import org.key_project.sed.algodebug.model.Execution;

public class SearchStrategy {
   protected boolean searchCompletedButNoBugFound = false;
   protected boolean bugFound = false;
   protected Execution bug;

   public SearchStrategy(){

   }

   public boolean searchCompletedButNoBugFound() {
      return searchCompletedButNoBugFound;
   }

   public boolean bugFound() {
      return bugFound;
   }
   
   public Execution getBug() {
      return bug;
   }
}