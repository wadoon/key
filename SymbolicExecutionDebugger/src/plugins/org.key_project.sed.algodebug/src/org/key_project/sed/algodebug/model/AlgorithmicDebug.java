package org.key_project.sed.algodebug.model;

import org.eclipse.debug.core.DebugException;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.algodebug.LinkAction.AlgorithmicDebugCorrectAnnotationLinkAction;
import org.key_project.sed.algodebug.LinkAction.AlgorithmicDebugFalseAnnotationLinkAction;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationType;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugCorrectAnnotation;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugCorrectAnnotationType;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugFalseAnnotation;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugFalseAnnotationType;
import org.key_project.sed.core.annotation.impl.HighlightAnnotation;
import org.key_project.sed.core.annotation.impl.HighlightAnnotationType;
import org.key_project.sed.core.model.ISEBranchCondition;
import org.key_project.sed.core.model.ISEBranchStatement;
import org.key_project.sed.core.model.ISEDebugTarget;
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
   private Call lastHighlightedCall;
   
   public AlgorithmicDebug() {
      path = null;
   }
   
   private CallTree path;
   
   public CallTree getPath(ISENode node){
      if(path == null){
         path = new CallTree();
         path.generatePaths(getRoot(node));
         //path.printPathsToConsoleWithIterators();
         }
      return path;
   }
   
   /**
    * Method to find the next node of the Symbolic Execution Tree that should be asked.
    * @param node    The selected {@link ISENode}.
    * @return        Next node to ask {@link ISENode} or null if all nodes have been visited.
    */
   //selectNode wählt den nächsten Knoten der noch nicht annotiert wurde.
   public ISENode selectNode(ISENode node){
      AlgorithmicTraversal at = new AlgorithmicTraversal();
      at.setStrategie(new TraversalStrategyPostOrder());
      
      return at.traverse(node);
   }
   
   /**
    * Method for calling the annotation methods.
    * @param shell   The current {@link Shell}.
    * @param node    The selected {@link ISENode}.
    * @param value   The state the Node should be annotated with. True for a "correct" annotation, false for a "false" annotation.
    */
   public void annotateNode(Shell shell, ISENode node, boolean value){
      
      AlgorithmicDebugCorrectAnnotationLinkAction ac = new AlgorithmicDebugCorrectAnnotationLinkAction();
      AlgorithmicDebugFalseAnnotationLinkAction af = new AlgorithmicDebugFalseAnnotationLinkAction();
      if(value)
         ac.run(shell, node);
      else
         af.run(shell, node);
      }
   
   public ISENode getRoot(ISENode node){
      try {
         if(node.getParent() == null) //Dann haben wir bereits den Root-Knoten gefunden
            return node;
         else if( node.getParent() instanceof ISEThread)
            return node.getParent();
         else
            return getRoot(node.getParent());
      }
      catch (DebugException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }

      return node;
   }
   
   /*
    * Markiert einen Call, also die Knoten zwischen dem dort gespeicherten Start und Endknoten
    */
   public void annotateCall(Call call, boolean bool){

      ISENode node = call.getRet();
      Shell shell = Display.getCurrent().getActiveShell();
      
      while(  !(node instanceof ISEThread) ){
//         try {
//            System.out.println("annotiere: "+node.getName().toString() +" und hasUnAnnotatedChildren(node) ist: "+hasUnAnnotatedChildren(node));
//         }
//         catch (DebugException e1) {
//            // TODO Auto-generated catch block
//            e1.printStackTrace();
//         }
         if(node == call.getCall() ){
            annotateNode(shell, node, bool); //annotieren
            break;
            }
         else if( ( (node instanceof ISEBranchCondition || node instanceof ISEBranchStatement) && hasUnAnnotatedChildren(node))){
            break;
         }
         else{
            annotateNode(shell, node, bool); //annotieren
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
   
   public void highlightCall(Call call){

      ISENode node = call.getRet();
      Shell shell = Display.getCurrent().getActiveShell();
      
      while(  !(node instanceof ISEThread)){
//         try {
//            System.out.println("++++Highlighte Node: "+node.getName().toString());
//         }
//         catch (DebugException e1) {
//            // TODO Auto-generated catch block
//            e1.printStackTrace();
//         }
            if(node == call.getCall()){
               highlightNode(shell, node); //annotieren
               break;
               }
            else{
               highlightNode(shell, node); //annotieren
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
         ISENode node = lastHighlightedCall.getRet();
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
   
 public void highlightNode(Shell shell, ISENode node) {  
  
    ISEAnnotationType annotationTypeHighlight = SEAnnotationUtil.getAnnotationtype(HighlightAnnotationType.TYPE_ID);   
    ISEAnnotation[] registeredAnnotationsHighlight = node.getDebugTarget().getRegisteredAnnotations(annotationTypeHighlight);
    
    ISEAnnotation annotationHighlight = ArrayUtil.search(registeredAnnotationsHighlight, new IFilter<ISEAnnotation>() {
       @Override
       public boolean select(ISEAnnotation element) {
          return element instanceof HighlightAnnotation; 
       }
    });
      
      if(annotationHighlight == null){
         ISEDebugTarget target = node.getDebugTarget();
         annotationHighlight = annotationTypeHighlight.createAnnotation();
         target.registerAnnotation(annotationHighlight);
      }

      //If AnnotationLink was not found, we create a new one and attach it to the node
        if(node.getAnnotationLinks(annotationTypeHighlight).length == 0){
           node.addAnnotationLink(annotationTypeHighlight.createLink(annotationHighlight, node));
        }     
   }
 
   /*
    * Gibt wahr zurück wenn es Kinder gibt die nicht korrekt annotiert wurden
    */
   private boolean hasUnAnnotatedChildren(ISENode node){
      try {
         //System.out.println("HasUnannotatedChildren:");
         for(ISENode child : node.getChildren()){
            //System.out.println("Checke: "+child.getName().toString());
            int len = child.getAnnotationLinks(SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugCorrectAnnotationType.TYPE_ID)).length;
            //System.out.println("Anzahl Correkt Markierungen:" +len);
            if(len == 0){ //Knoten noch nicht korrekt markiert
               //System.out.println("Noch nicht markiertes Child gefunden: " + child.getName().toString());
               return true;
               }
         }
      }
      catch (DebugException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
      return false;
   }
   
}