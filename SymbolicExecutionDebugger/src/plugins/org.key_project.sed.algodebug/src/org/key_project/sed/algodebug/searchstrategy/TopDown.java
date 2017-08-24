package org.key_project.sed.algodebug.searchstrategy;

import org.key_project.sed.algodebug.model.Execution;
import org.key_project.sed.algodebug.util.MCTUtil;

public class TopDown extends SearchStrategy implements ISearchStrategy {

   private Execution lastAskedExecution;
   private Execution root;
   /*
    * return null wenn kein nächster Method Call gefunden werden kann
    * -----> weil der Baum komplett abgesucht wurde
    * -----> weil ein Bug gefunden wurde
    * return nächsten abzufragenden Method Call sonst
    */
   @Override
   public Execution getNext(Execution tree) {
      if(lastAskedExecution == null){
         root = tree;
         lastAskedExecution = tree;
         return tree;
      }
      else if(lastAskedExecution.isRoot() && lastAskedExecution.getCorrectness() == 'c'){
         searchCompletedButNoBugFound = true;
         lastAskedExecution.setExecutionTreeCompletelySearched(true);
         return null;
      }
      else if(lastAskedExecution.getCorrectness() == 'f' ){
         if(MCTUtil.isEveryChildMarkedAs(lastAskedExecution, 'c')){
            bugFound = true;
            bug = lastAskedExecution;
            return null;
         }
         for(Execution child : lastAskedExecution.getListOfCalledMethods()){
            if(child.getCorrectness() == 'u'){
               lastAskedExecution = child;
               return child;
            }
         }
         //Methode inkorrekt und alle Aufrufe korrekt: Methode ist Bug
         bugFound = true;
         bug = lastAskedExecution;
         return null;
      }
      else if(lastAskedExecution.getCorrectness() == 'c'){
         //            SETUtil.annotateMethodCallCorrect(lastAskedMethod);
         if(!lastAskedExecution.isRoot()){
            if(MCTUtil.isEveryChildMarkedAs(lastAskedExecution.getParent(), 'c')){
               bugFound = true;
               bug = lastAskedExecution.getParent();
               return null;
            }
         }
         for(Execution sibling : lastAskedExecution.getParent().getListOfCalledMethods()){
            if(sibling.getCorrectness() == 'u'){
               lastAskedExecution = sibling;
               return sibling;
            }
         }
      }
      //kein Bug gefunden
      root.setExecutionTreeCompletelySearched(true);
      searchCompletedButNoBugFound = true;
      return null;
   }

   public void reset(){
      lastAskedExecution = null;
      root = null;
      searchCompletedButNoBugFound = false;
   }

   @Override
   public void setExecutionCorrectness(Execution execution, char correctness) {
      execution.setExecutionCorrectness(correctness);
   }

   @Override
   public boolean treeCompletelySearched() {
      if(root.getCorrectness() == 'c')
         return true;
      else 
         return false;
   }
}
