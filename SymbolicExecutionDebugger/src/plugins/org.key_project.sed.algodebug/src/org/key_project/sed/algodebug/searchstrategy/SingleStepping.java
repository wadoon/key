package org.key_project.sed.algodebug.searchstrategy;

import org.key_project.sed.algodebug.model.Execution;
import org.key_project.sed.algodebug.util.MCTUtil;

public class SingleStepping extends SearchStrategy implements ISearchStrategy {

   /*
    * the execution that is the root of the execution tree
    */
   private Execution root;

   /*
    * (non-Javadoc)
    * @see org.key_project.sed.algodebug.searchstrategy.ISearchStrategy#getNext(org.key_project.sed.algodebug.model.Execution)
    */
   @Override
   public Execution getNext(Execution tree) {
      if(root == null)
         root = tree;
      switch(tree.getCorrectness()){
      case 'f':{
         bugFound = true;
         bug = tree;
         return null;
      }
      case 'c':{
         root.setExecutionTreeCompletelySearched(true);
         searchCompletedButNoBugFound = true;
         return null;
      }
      case 'u':{
         for(Execution child : tree.getListOfCalledMethods()){
            switch(child.getCorrectness()){
            case 'f':         
               bugFound = true;
               bug = child;
               return null;
            case 'c':
               continue;
            case 'u':
               return getNext(child);
            }
         }
         return tree;
      }
      }
      return null;
   }

   /*
    * (non-Javadoc)
    * @see org.key_project.sed.algodebug.searchstrategy.ISearchStrategy#setExecutionCorrectness(org.key_project.sed.algodebug.model.Execution, char)
    */
   @Override
   public void setExecutionCorrectness(Execution execution, char correctness) {
      execution.setExecutionCorrectness(correctness);
      if(correctness == 'f')
         MCTUtil.annotateSETNodesOfABuggyExecution(execution);
      if(correctness == 'c')
         MCTUtil.annotateExecutionPartialCorrect(execution);
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

   /*
    * (non-Javadoc)
    * @see org.key_project.sed.algodebug.searchstrategy.ISearchStrategy#reset()
    */
   @Override
   public void reset() {
      root = null;
      searchCompletedButNoBugFound = false;
   }
}