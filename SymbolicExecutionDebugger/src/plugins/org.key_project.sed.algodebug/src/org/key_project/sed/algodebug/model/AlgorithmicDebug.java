package org.key_project.sed.algodebug.model;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.algodebug.searchstrategy.ISearchStrategy;
import org.key_project.sed.algodebug.util.SETUtil;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationType;
import org.key_project.sed.core.annotation.impl.HighlightAnnotation;
import org.key_project.sed.core.annotation.impl.HighlightAnnotationType;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.util.SEAnnotationUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;

/**
 * @author Peter Schauberger
 */
public class AlgorithmicDebug  {

   //Letzten Call zwischenspeichern um Rückgängigmachen des Highlighting in unhighlight zu ermöglichen
   private Execution lastHighlightedCall;
   public Execution getLastHighlightedCall(){
      return lastHighlightedCall;
   }

   private ISearchStrategy searchStrategy;

   public AlgorithmicDebug() {
      listOfExecutionTrees = new ListOfExecutionTrees();
   }
   private ListOfExecutionTrees listOfExecutionTrees;

   private boolean bugFound = false;

   private Execution bug;

   private boolean searchCompletedButNoBugFound = false;

   public void generateTree(ISENode root){
      listOfExecutionTrees.generateListOfExecutionTrees(root);
      listOfExecutionTrees.addParentsToTree();
//      listOfExecutionTrees.printTree();
      listOfExecutionTrees.printTreeAsGraphviz();
   }

   public Execution getBug(){
      return bug;
   }

   private Execution actualExecutionTree;

   /*
    * return Method Call wenn ein nächster Knoten zum abfragen gefunden werden konnte.
    * return null wenn ein Bug gefunden wurde oder alle Bäume komplett abgesucht wurden
    * -----> frage bei return null in der Such-Methode nach was los ist und setze bugFound oder searchCompletedButNoBugFound
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
               else // 
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
         else // 
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
    * return null wenn ein Bug gefunden wurde oder der ganze Baum durchsucht wurde
    * return Method Call wenn ein nächster Method Call gefunden wurde der abgefragt werden soll
    */
   private Execution searchBugInExecutionTree(Execution executionTree){
      return searchStrategy.getNext(executionTree);
   }

   public Execution getNext(){
      return searchBugInListOfExecutionTrees();
   }

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
            // TODO Auto-generated catch block
            e.printStackTrace();
         }
      }
      lastHighlightedCall = call;
   }

   public void unhighlight(){

      if(lastHighlightedCall != null){
         ISENode node = lastHighlightedCall.getExecutionReturn();
         ISEAnnotationType annotationTypeHighlight = SEAnnotationUtil.getAnnotationtype(HighlightAnnotationType.TYPE_ID);
         ISEAnnotation[]  registeredAnnotationsHighlight = node.getDebugTarget().getRegisteredAnnotations(annotationTypeHighlight);

         try {
            while(  !(node == lastHighlightedCall.getCall().getParent())){ //!(node instanceof ISEThread) ){ //
               //System.out.println("----UNhighlighte Node: "+node.getName().toString()+ " vom Typ: "+node.getNodeType());

               ISEAnnotation annotationHighlight = ArrayUtil.search(registeredAnnotationsHighlight, new IFilter<ISEAnnotation>() {
                  @Override
                  public boolean select(ISEAnnotation element) {
                     return element instanceof HighlightAnnotation; 
                  }
               });
               if(annotationHighlight != null){
                  node.removeAnnotationLink(annotationTypeHighlight.createLink(annotationHighlight, node));
               }

               try {
                  node = node.getParent();
               }
               catch (DebugException e) {
                  // TODO Auto-generated catch block
                  e.printStackTrace();
               }
            }
         }
         catch (DebugException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
         }
      }
   }

   /*
    * Markiert einen Call, also die Knoten zwischen dem dort gespeicherten Start und Endknoten
    */
   public void markCall(Execution execution, char correctness){
      searchStrategy.setExecutionCorrectness(execution, correctness);
   }

   public void setSearchStrategy(ISearchStrategy strategy) {
      searchStrategy = strategy;      
   }

   public boolean bugFound() {
      return bugFound;
   }

   public boolean searchCompletedButNoBugFound() {
      return searchCompletedButNoBugFound;
   }
}