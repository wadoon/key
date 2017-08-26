package org.key_project.sed.algodebug.model;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.algodebug.searchstrategy.ISearchStrategy;
import org.key_project.sed.algodebug.util.SETUtil;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEThread;

/**
 * @author Peter Schauberger
 */
public class AlgorithmicDebug  {

   /*
    * The last execution that has been highlighted
    */
   private Execution lastHighlightedCall;
   
   /*
    * @return The last highlighted execution
    */
   public Execution getLastHighlightedExecution(){
      return lastHighlightedCall;
   }

   /*
    * The search-strategy used for algorithmic debugging
    */
   private ISearchStrategy searchStrategy;

   /*
    * Constructor
    */
   public AlgorithmicDebug() {
      listOfExecutionTrees = new ListOfExecutionTrees();
   }
   
   /*
    * 
    */
   private ListOfExecutionTrees listOfExecutionTrees;

   /*
    * Flag to indicate if a bug was found by the algorithmic debugging process
    */
   private boolean bugFound = false;

   /*
    * The bug that was found.
    */
   private Execution bug;

   /*
    * Flag to indicate if all execution trees have been searched but no bug was found
    */
   private boolean searchCompletedButNoBugFound = false;

   /*
    * 
    */
   public void generateTree(ISENode root){
      listOfExecutionTrees.generateListOfExecutionTrees(root);
      listOfExecutionTrees.addParentsToTree();
//      listOfExecutionTrees.printTree();
//      listOfExecutionTrees.printTreeAsGraphviz();
   }

   /*
    * returns the execution that has been identified as bug
    */
   public Execution getBug(){
      return bug;
   }

   /*
    * the execution tree that is searched at the moment
    */
   private Execution actualExecutionTree;

   /*
    * @return execution if next execution was found that has to be asked
    * @return null if either a bug was found or all execution trees were searched withouot finding a bug 
    */
   public Execution searchBugInListOfExecutionTrees(){
      if(actualExecutionTree == null)
         actualExecutionTree = listOfExecutionTrees.getListOfExecutionTrees().get(0);
      if(actualExecutionTree.completelySearched()){
         for(Execution executionTree :listOfExecutionTrees.listOfExecutionTrees){
            if(executionTree.getExecutionTreeCompletelySearched())
               continue;
            else{
               actualExecutionTree = executionTree;
               searchStrategy.reset();
               Execution maybeABuggyCall = searchBugInExecutionTree(executionTree);
               if(maybeABuggyCall != null){
                  return maybeABuggyCall;
               }
               else
                  if(searchStrategy.bugFound()){
                     bug = searchStrategy.getBug();
                     bugFound = true;
                     return null;
                  }
                  else if(searchStrategy.searchCompletedButNoBugFound()){
                     continue;
                  }
            }
         }
      }
      else{
         Execution maybeABuggyCall = searchBugInExecutionTree(actualExecutionTree);
         if(maybeABuggyCall != null){
            return maybeABuggyCall;
         }
         else 
            if(searchStrategy.bugFound()){
               bug = searchStrategy.getBug();
               bugFound = true;
               return null;
            }
            else if(searchStrategy.searchCompletedButNoBugFound()){
               return searchBugInListOfExecutionTrees();
            }
      }
      //Hier kommen wir hin wenn alle Trees durchlaufen wurden und kein Bug gefunden wurde
      searchCompletedButNoBugFound = true;
      return null;
   }

   /*
    * @returns null is a bug was found or the whole execution tree was searched without finding a bug or 
    * @returns the next execution that has to be asked
    */
   private Execution searchBugInExecutionTree(Execution executionTree){
      return searchStrategy.getNext(executionTree);
   }

   /*
    * uses the search-strategy to get the next execution that should be asked to the user from the actual execution tree 
    */
   public Execution getNext(){
      return searchBugInListOfExecutionTrees();
   }

   /*
    * adds the highlight annotations toall SET nodes that belong to the next execution that is asked to the user
    */
   public void highlightCall(Execution call){

      ISENode node = call.getExecutionReturn();

      while(  !(node instanceof ISEThread)){
         if(node == call.getCall()){
            SETUtil.highlightNode(node); //annotieren
            break;
         }
         else{
            SETUtil.highlightNode(node); //annotieren
         }

         try {
            node = node.getParent();
         }
         catch (DebugException e) {
            e.printStackTrace();
         }
      }
      lastHighlightedCall = call;
   }

   /*
    * removes the highlight annotations from all SET nodes that belong to the last highlited execution
    */
   public void unhighlight(){
      SETUtil.unhighlight(lastHighlightedCall);
   }

   /*
    * Markiert einen Call, also die Knoten zwischen dem dort gespeicherten Start und Endknoten
    */
   public void markCall(Execution execution, char correctness){
      searchStrategy.setExecutionCorrectness(execution, correctness);
   }

   /*
    * sets the search strategy für algorithmic debugging
    * @param the search-strategy that shound be used
    */
   public void setSearchStrategy(ISearchStrategy strategy) {
      searchStrategy = strategy;
   }

   /*
    * returns true if a bug was found
    */
   public boolean bugFound() {
      return bugFound;
   }

   /*
    * returns true if search was completed but no bug was found.
    * None of the execution trees has a bug.
    */
   public boolean searchCompletedButNoBugFound() {
      return searchCompletedButNoBugFound;
   }
}