package org.key_project.sed.algodebug.searchstrategy2;

import org.key_project.sed.algodebug.model2.MethodCall;

public class SearchStrategy {
   protected boolean searchCompletedButNoBugFound = false;
   protected boolean bugFound = false;
   protected MethodCall bug;

   public SearchStrategy(){
      
   }
   
   public boolean seachCompletedButNoBugFound() {
      return searchCompletedButNoBugFound;
   }
   
   public boolean bugFound() {
      return bugFound;
   }
   
}