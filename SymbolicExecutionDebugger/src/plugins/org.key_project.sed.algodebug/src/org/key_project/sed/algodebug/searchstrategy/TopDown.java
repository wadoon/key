package org.key_project.sed.algodebug.searchstrategy;

import org.key_project.sed.algodebug.model.Execution;
import org.key_project.sed.algodebug.util.ExecutionTreeUtil;

public class TopDown extends SearchStrategy implements ISearchStrategy {

   /*
    * the last execution that was returned
    * used as a starting point for the next search
    */
   private Execution lastAskedExecution;
   
   /*
    * the execution that is the root node of the execution tree
    */
   private Execution root;
   
   /*
    * return null if the execution tree was searched completely or
    * return null if a buggy execution was found
    * return next execution to be asked to the user otherwise
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
         if(ExecutionTreeUtil.isEveryChildMarkedAs(lastAskedExecution, 'c')){
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
            if(ExecutionTreeUtil.isEveryChildMarkedAs(lastAskedExecution.getParent(), 'c')){
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

   /*
    * (non-Javadoc)
    * @see org.key_project.sed.algodebug.searchstrategy.ISearchStrategy#reset()
    */
   public void reset(){
      lastAskedExecution = null;
      root = null;
      searchCompletedButNoBugFound = false;
   }

   /*
    * (non-Javadoc)
    * @see org.key_project.sed.algodebug.searchstrategy.ISearchStrategy#setExecutionCorrectness(org.key_project.sed.algodebug.model.Execution, char)
    */
   @Override
   public void setExecutionCorrectness(Execution execution, char correctness) {
      if(correctness == 'c'){
         execution.setExecutionCorrectnessIncludingSubMethods(correctness);
         ExecutionTreeUtil.annotateExecutionPartialCorrect(execution);
//         MCTUtil.annotateExecutionRecursively(execution,correctness);
      }
      if(correctness == 'f'){
         execution.setExecutionCorrectness(correctness);
         ExecutionTreeUtil.annotateSETNodesOfExecutionExcludingSubExecutions(execution, 'f');
      }
   }

   /*
    * (non-Javadoc)
    * @see org.key_project.sed.algodebug.searchstrategy.ISearchStrategy#treeCompletelySearched()
    */
   @Override
   public boolean treeCompletelySearched() {
      if(root.getCorrectness() == 'c')
         return true;
      else 
         return false;
   }
}
