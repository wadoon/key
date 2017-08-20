package org.key_project.sed.algodebug.model2;

import java.util.ArrayList;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.algodebug.searchstrategy2.ISearchStrategy;
import org.key_project.sed.algodebug.util.MCTUtil;
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
public class AlgorithmicDebug2  {

   //Letzten Call zwischenspeichern um Rückgängigmachen des Highlighting in unhighlight zu ermöglichen
   private MethodCall lastHighlightedCall;
   public MethodCall getLastHighlightedCall(){
      return lastHighlightedCall;
   }

   private ISearchStrategy searchStrategy;

   public AlgorithmicDebug2() {
      listOfMethodCallTrees = new ListOfMethodCallTrees();
   }
   private ListOfMethodCallTrees listOfMethodCallTrees;

   private boolean bugFound = false;

   private MethodCall bug;

   private boolean searchCompletedButNoBugFound = false;

   public void generateTree(ISENode root){
      listOfMethodCallTrees.generateListOfMethodCallTrees(root);
      listOfMethodCallTrees.addParentsToTree();
      //      listOfMethodCallTrees.printTree();
   }

   public void markBuggyMethodCall(MethodCall methodCall){
      searchStrategy.markBug(methodCall, 'f');
   }

   public MethodCall getBug(){
      return bug;
   }
   
   private MethodCall actualMethodCallTree;

   /*
    * return Method Call wenn ein nächster Knoten zum abfragen gefunden werden konnte.
    * return null wenn ein Bug gefunden wurde oder alle Bäume komplett abgesucht wurden
    * -----> frage bei return null in der Such-Methode nach was los ist und setze bugFound oder searchCompletedButNoBugFound
    */
   public MethodCall searchBugInListOfMethodCallTrees(){
      if(actualMethodCallTree == null)
         actualMethodCallTree = listOfMethodCallTrees.getListOfMethodCallTrees().get(0);
      if(actualMethodCallTree.completelySearched()){
         for(MethodCall methodCallTree :listOfMethodCallTrees.listOfMethodCallTrees){
            if(methodCallTree.getMethodCallTreeCompletelySearched())
               continue;
            else{
               actualMethodCallTree = methodCallTree;
               searchStrategy.reset();
               MethodCall maybeABuggyCall = searchBugInMethodCallTree(methodCallTree);
               if(maybeABuggyCall != null){
                  return maybeABuggyCall;
               }
               else // 
                  if(searchStrategy.bugFound()){
                     bug = searchStrategy.getBug();
                     bugFound = true;
                     return null;
                  }
                  else if(searchStrategy.seachCompletedButNoBugFound()){
                     continue;
                  }
            }
         }
      }
      else{
         MethodCall maybeABuggyCall = searchBugInMethodCallTree(actualMethodCallTree);
         if(maybeABuggyCall != null){
            return maybeABuggyCall;
         }
         else // 
            if(searchStrategy.bugFound()){
               bug = searchStrategy.getBug();
               bugFound = true;
               return null;
            }
            else if(searchStrategy.seachCompletedButNoBugFound()){
               return searchBugInListOfMethodCallTrees();
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
   private MethodCall searchBugInMethodCallTree(MethodCall methodCallTree){
      return searchStrategy.getNext(methodCallTree);
   }

   private boolean wasEveryCallOfExecutionTreeAsked(MethodCall tree){
      boolean childrenCorrectness = true;
      for(MethodCall child : tree.getListOfCalledMethods()){
         childrenCorrectness = childrenCorrectness & wasEveryCallOfExecutionTreeAsked(child);
         if(!childrenCorrectness)
            return false;
      }
      if(tree.getCorrectness() == 'u')
         return false;
      else 
         return true;
   }

   public MethodCall getNext(){
      return searchBugInListOfMethodCallTrees();
   }

   public void highlightCall(MethodCall call){

      ISENode node = call.getMethodReturn();

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
         ISENode node = lastHighlightedCall.getMethodReturn();
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
   public void markCall(MethodCall methodCall, char correctness){
      searchStrategy.setMethodCallCorrectness(methodCall, correctness);
   }

   public void markBug(MethodCall methodCall, char correctness){
      searchStrategy.markBug(methodCall, correctness); 
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