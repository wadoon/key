package org.key_project.sed.algodebug.searchstrategy;

import org.key_project.sed.algodebug.model.Execution;

public class SearchStrategy {
   protected boolean searchCompletedButNoBugFound = false;
   protected boolean bugFound = false;
   protected Execution bug;

   /*
    * constructor
    */
   public SearchStrategy(){
   }

   /*
    * returns true if the execution tree was completely searched
    */
   public boolean searchCompletedButNoBugFound() {
      return searchCompletedButNoBugFound;
   }

   /*
    * returns true if a bug was found
    */
   public boolean bugFound() {
      return bugFound;
   }
   
   /*
    * returns the buggy execution if a bug was found
    */
   public Execution getBug() {
      return bug;
   }
}