package org.key_project.sed.algodebug.model;

import org.eclipse.debug.core.DebugException;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
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
      tree = null;
   }

   private CallTree tree;
   private ISENode root;
   /*
    * getCallTree
    * Der Knoten welcher den Anfangspunkt darstellt wird immer übergeben
    */

   public CallTree getCallTree(ISENode node, String strategy){
      if(tree == null){
         tree = new CallTree();
         if(strategy.equals("Bottom Up"))
            tree.generateCallTree(getRoot(node), "BottomUp");
         else if(strategy.equals("Top Down"))
            tree.generateCallTree(getRoot(node), "TopDown");
         //         path.printPathsToConsoleWithIterators();
      }
      return tree;
   }

   public CallTree getCallTree(){
      return tree;
   }
   public void highlightCall(Call call){

      ISENode node = call.getRet();

      while(  !(node instanceof ISEThread)){
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

   /*
    * returns the root node of the symbolic tree
    * @author Peter Schauberger
    */
   public ISENode getRoot(ISENode node){
      //      System.out.println("getRoot");
      try {
         if(node.getParent() == null){ //Dann haben wir bereits den Root-Knoten gefunden
            root = node;
            return node;
         }
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
      call.setCorrectness('c');
      annotateNodes(call, bool);
   }

   /*
    * Annotiert die Nodes eines Call mit dem Wert von bool
    * @params call - der Call dessen Knoten annotiert werden sollen
    * @param bool - der Wert den die Knoten erhalten sollen
    */

   private void annotateNodes(Call call, boolean bool){

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

   public void removeAllAlgoDebugAnnotations(ISENode node){
      removeAnnotations(node);
      try {
         if(node.hasChildren())
            for(ISENode child : node.getChildren()){ //Es gibt Kind-Knoten: Für jeden neuen Pfad hinzufügen
               removeAllAlgoDebugAnnotations(child);
            }
      }
      catch (DebugException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
   }

   private void removeAnnotations(ISENode node){
      this.registeredAnnotationsFalse = node.getDebugTarget().getRegisteredAnnotations(annotationTypeFalse);
      this.registeredAnnotationsCorrect = node.getDebugTarget().getRegisteredAnnotations(annotationTypeCorrect);

      ISEAnnotation annotationFalse = ArrayUtil.search(registeredAnnotationsFalse, new IFilter<ISEAnnotation>() {
         @Override
         public boolean select(ISEAnnotation element) {
            return element instanceof AlgorithmicDebugFalseAnnotation; 
         }
      });

      ISEAnnotation annotationCorrect = ArrayUtil.search(registeredAnnotationsCorrect, new IFilter<ISEAnnotation>() {
         @Override
         public boolean select(ISEAnnotation element) {
            return element instanceof AlgorithmicDebugCorrectAnnotation; 
         }
      });

      if(node.getAnnotationLinks(annotationTypeCorrect).length != 0)
         node.removeAnnotationLink(annotationTypeCorrect.createLink(annotationCorrect, node));
      if(node.getAnnotationLinks(annotationTypeFalse).length != 0)
         node.removeAnnotationLink(annotationTypeFalse.createLink(annotationFalse, node));
   }

   /**
    * Method for calling the annotation methods.
    * @param shell   The current {@link Shell}.
    * @param node    The selected {@link ISENode}.
    * @param value   The state the Node should be annotated with. True for a "correct" annotation, false for a "false" annotation.
    */
   public void annotateNode(Shell shell, ISENode node, boolean value){
      if(value)
         annotateCorrect(shell, node);
      else
         annotateFalse(shell, node);
   }

   private ISEAnnotationType annotationTypeCorrect = SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugCorrectAnnotationType.TYPE_ID);
   private ISEAnnotationType annotationTypeFalse = SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugFalseAnnotationType.TYPE_ID);

   private ISEAnnotation[] registeredAnnotationsCorrect;
   private ISEAnnotation[] registeredAnnotationsFalse;

   /**
    * @author Peter Schauberger
    */
   public void annotateCorrect(Shell shell, ISENode node) {
      this.registeredAnnotationsCorrect = node.getDebugTarget().getRegisteredAnnotations(annotationTypeCorrect);
      this.registeredAnnotationsFalse = node.getDebugTarget().getRegisteredAnnotations(annotationTypeFalse);

      ISEAnnotation annotationCorrect = ArrayUtil.search(registeredAnnotationsCorrect, new IFilter<ISEAnnotation>() {
         @Override
         public boolean select(ISEAnnotation element) {
            return element instanceof AlgorithmicDebugCorrectAnnotation; 
         }
      });

      if(annotationCorrect == null){
         ISEDebugTarget target = node.getDebugTarget();
         annotationCorrect = annotationTypeCorrect.createAnnotation();
         target.registerAnnotation(annotationCorrect);
      }

      //If AnnotationLink was not found, we create a new one and attach it to the node
      if(node.getAnnotationLinks(annotationTypeCorrect).length == 0){
         if(node.getAnnotationLinks(annotationTypeFalse).length == 0){

            node.addAnnotationLink(annotationTypeCorrect.createLink(annotationCorrect, node));
         }
         else{
            ISEAnnotation annotationFalse = ArrayUtil.search(registeredAnnotationsFalse, new IFilter<ISEAnnotation>() {
               @Override
               public boolean select(ISEAnnotation element) {
                  return element instanceof AlgorithmicDebugFalseAnnotation; 
               }
            });
            node.removeAnnotationLink(annotationTypeFalse.createLink(annotationFalse, node));
            node.addAnnotationLink(annotationTypeCorrect.createLink(annotationCorrect, node));
         }
      }
   }

   /**
    * @author Peter Schauberger
    * @throws DebugException 
    */
   private void annotateNext(Shell shell, ISENode node){
      try {
         ISENode parent = node.getParent();

         if(!(parent instanceof ISEBranchStatement))
            annotateCorrect (shell, parent);

         else{
            boolean childNotCorrect = false;
            for(ISENode child : parent.getChildren()){
               if(child.getAnnotationLinks(annotationTypeCorrect).length == 0) {
                  childNotCorrect = true;              
                  break;
               }
            }
            if(!childNotCorrect)
               annotateCorrect (shell, parent);              
         }
      }
      catch (DebugException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
   }

   public void annotateFalse(Shell shell, ISENode node) {
      //TODO: Hier muss die Annotation erzeugt und registriert werden

      this.registeredAnnotationsFalse = node.getDebugTarget().getRegisteredAnnotations(annotationTypeFalse);
      this.registeredAnnotationsCorrect = node.getDebugTarget().getRegisteredAnnotations(annotationTypeCorrect);

      ISEDebugTarget target = node.getDebugTarget();
      ISEAnnotation annotationFalse = ArrayUtil.search(registeredAnnotationsFalse, new IFilter<ISEAnnotation>() {
         @Override
         public boolean select(ISEAnnotation element) {
            return element instanceof AlgorithmicDebugFalseAnnotation; 
         }
      });
      if (annotationFalse == null){
         annotationFalse = annotationTypeFalse.createAnnotation();
         target.registerAnnotation(annotationFalse);}

      ISEAnnotation annotationCorrect = ArrayUtil.search(registeredAnnotationsCorrect, new IFilter<ISEAnnotation>() {
         @Override
         public boolean select(ISEAnnotation element) {
            return element instanceof AlgorithmicDebugCorrectAnnotation; 
         }
      });

      if (annotationCorrect == null){
         annotationCorrect = annotationTypeCorrect.createAnnotation();
         target.registerAnnotation(annotationCorrect);}

      //If AnnotationLink was not found, we create a new one and attach it to the node
      if(node.getAnnotationLinks(annotationTypeFalse).length == 0){
         if(annotationCorrect == null || node.getAnnotationLinks(annotationTypeCorrect).length == 0){
            node.addAnnotationLink(annotationTypeFalse.createLink(annotationFalse, node));
         }
         else{ 
            node.removeAnnotationLink(annotationTypeCorrect.createLink(annotationCorrect, node));
            node.addAnnotationLink(annotationTypeFalse.createLink(annotationFalse, node));
         }
      }
   }

   private Shell shell = Display.getCurrent().getActiveShell();

   /*
    * Annotiert die Nodes eines Call rückwärts vom Return Knoten aus als falsch
    */

   public void annotateCallFalse(Call call){

      ISENode node = call.getRet();

      while(  !(node instanceof ISEThread) ){
         //         try {
         //            System.out.println("annotiere: "+node.getName().toString() +" und hasUnAnnotatedChildren(node) ist: "+hasUnAnnotatedChildren(node));
         //         }
         //         catch (DebugException e1) {
         //            // TODO Auto-generated catch block
         //            e1.printStackTrace();
         //         }
         if(node == call.getCall() ){
            annotateNode(shell, node,false); //annotieren
            break;
         }
         else{
            if(node.getAnnotationLinks(SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugCorrectAnnotationType.TYPE_ID)).length == 0 ) //wenn node keine korrekt Annotationen enthält wird er falsch markiert.
               annotateNode(shell, node, false); //annotieren
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

   public boolean isCorrectAnnotated(ISENode node){
      ISEAnnotationType annotationTypeCorrect = SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugCorrectAnnotationType.TYPE_ID);
      ISEAnnotation[] registeredAnnotationsCorrect = node.getDebugTarget().getRegisteredAnnotations(annotationTypeCorrect);

      ISEAnnotation annotationCorrect = ArrayUtil.search(registeredAnnotationsCorrect, new IFilter<ISEAnnotation>() {
         @Override
         public boolean select(ISEAnnotation element) {
            return element instanceof AlgorithmicDebugCorrectAnnotation; 
         }
      });

      if(annotationCorrect != null)
         return true;
      else return false;
   }

}