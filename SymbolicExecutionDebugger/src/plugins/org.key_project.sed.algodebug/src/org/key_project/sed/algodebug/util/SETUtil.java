package org.key_project.sed.algodebug.util;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.algodebug.model.Execution;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationType;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugBugAnnotation;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugBugAnnotationType;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugCorrectAnnotation;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugCorrectAnnotationType;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugFalseAnnotation;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugFalseAnnotationType;
import org.key_project.sed.core.annotation.impl.HighlightAnnotation;
import org.key_project.sed.core.annotation.impl.HighlightAnnotationType;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.util.SEAnnotationUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;

/*
 * Die Klasse SETUtil enthält Hilfsklassen die auf dem SET arbeiten und der Übersichtlichkeit ausgelagert wurden.
 */
public class SETUtil {
   private static ISEAnnotationType annotationTypeCorrect = SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugCorrectAnnotationType.TYPE_ID);
   private static ISEAnnotationType annotationTypeFalse = SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugFalseAnnotationType.TYPE_ID);
   private static ISEAnnotationType annotationTypeBug = SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugBugAnnotationType.TYPE_ID);
   private static ISEAnnotationType annotationTypeHighlight = SEAnnotationUtil.getAnnotationtype(HighlightAnnotationType.TYPE_ID);


   private static ISEAnnotation[] registeredAnnotationsCorrect;
   private static ISEAnnotation[] registeredAnnotationsFalse;
   private static ISEAnnotation[] registeredAnnotationsBug;
   private static ISEAnnotation[] registeredAnnotationsHighlight;

   private static ISEAnnotation annotationCorrect = annotationTypeCorrect.createAnnotation();
   private static ISEAnnotation annotationFalse = annotationTypeFalse.createAnnotation();
   private static ISEAnnotation annotationBug = annotationTypeBug.createAnnotation();
   private static ISEAnnotation annotationHighlight = annotationTypeHighlight.createAnnotation();

   /*
    * initialize the annotations that are used to create the annotation links
    * @param node a node of the SET used to get the debug target hat is needed to create the annotations
    */
   public static void init(ISENode node){
      ISEDebugTarget target = node.getDebugTarget();

      annotationCorrect = ArrayUtil.search(registeredAnnotationsCorrect, new IFilter<ISEAnnotation>() {
         @Override
         public boolean select(ISEAnnotation element) {
            return element instanceof AlgorithmicDebugCorrectAnnotation; 
         }
      });
      if (annotationCorrect == null){
         annotationCorrect = annotationTypeCorrect.createAnnotation();
         target.registerAnnotation(annotationCorrect);
      }

      annotationFalse = ArrayUtil.search(registeredAnnotationsFalse, new IFilter<ISEAnnotation>() {
         @Override
         public boolean select(ISEAnnotation element) {
            return element instanceof AlgorithmicDebugFalseAnnotation; 
         }
      });
      if (annotationFalse == null){
         annotationFalse = annotationTypeFalse.createAnnotation();
         target.registerAnnotation(annotationFalse);
      }

      annotationBug = ArrayUtil.search(registeredAnnotationsBug, new IFilter<ISEAnnotation>() {
         @Override
         public boolean select(ISEAnnotation element) {
            return element instanceof AlgorithmicDebugBugAnnotation; 
         }
      });
      if (annotationBug == null){
         annotationBug = annotationTypeBug.createAnnotation();
         target.registerAnnotation(annotationBug);
      }

      annotationHighlight = ArrayUtil.search(registeredAnnotationsHighlight, new IFilter<ISEAnnotation>() {
         @Override
         public boolean select(ISEAnnotation element) {
            return element instanceof HighlightAnnotation; 
         }
      });
      if (annotationHighlight == null){
         annotationHighlight = annotationTypeHighlight.createAnnotation();
         target.registerAnnotation(annotationHighlight);
      }
   }

   /*
    * removes the highlight annotation of the ISENodes of the give execution
    */
   public static void unhighlight(Execution lastHighlightedCall){

      if(lastHighlightedCall != null){
         ISENode node = lastHighlightedCall.getExecutionReturn();

         try {
            while(  !(node == lastHighlightedCall.getCall().getParent())){ //!(node instanceof ISEThread) ){ //
               //System.out.println("----UNhighlighte Node: "+node.getName().toString()+ " vom Typ: "+node.getNodeType());

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
    * adds the highlight annotation to the given ISENode
    */
   public static void highlightNode(ISENode node) {  

      //If AnnotationLink was not found, we create a new one and attach it to the node
      if(node.getAnnotationLinks(annotationTypeHighlight).length == 0){
         node.addAnnotationLink(annotationTypeHighlight.createLink(annotationHighlight, node));
      }     
   }

   /*
    * returns the root node of the symbolic tree
    * @author Peter Schauberger
    */
   public static ISENode getRoot(ISENode node){
      try {
         if(node.getParent() == null){ //Dann haben wir bereits den Root-Knoten gefunden
            return node;
         }
         else if( node.getParent() instanceof ISEThread){
            return node.getParent();}
         else{

            return getRoot(node.getParent());
         }
      }
      catch (DebugException e) {
         e.printStackTrace();
      }
      return null;
   }

   /*
    * removes all used annotations from all ISENodes of the SET
    * @param node the root of the SET
    */
   public static void removeAllAlgoDebugAnnotations(ISENode node){
      if(node != null){
         removeAnnotations(node);
         try {
            if(node.hasChildren())
               for(ISENode child : node.getChildren()){ //Es gibt Kind-Knoten: Für jeden neuen Pfad hinzufügen
                  removeAllAlgoDebugAnnotations(child);
               }
         }
         catch (DebugException e) {
            e.printStackTrace();
         }}
   }

   /*
    * removes the annotationTypeCorrect annotation, the annotationTypeFalse annotation and annotationTypeHighlight annotation of the given ISENode
    * @param node the ISENode from which the annotations should be removed
    */
   public static void removeAnnotations(ISENode node){
      if(node.getAnnotationLinks(annotationTypeCorrect).length != 0)
         node.removeAnnotationLink(annotationTypeCorrect.createLink(annotationCorrect, node));
      if(node.getAnnotationLinks(annotationTypeFalse).length != 0)
         node.removeAnnotationLink(annotationTypeFalse.createLink(annotationFalse, node));
      if(node.getAnnotationLinks(annotationTypeBug).length != 0)
         node.removeAnnotationLink(annotationTypeBug.createLink(annotationBug, node));
      if(node.getAnnotationLinks(annotationTypeHighlight).length != 0)
         node.removeAnnotationLink(annotationTypeHighlight.createLink(annotationHighlight, node));
   }

   /**
    * Method for calling the annotation methods.
    * @param shell   The current {@link Shell}.
    * @param node    The selected {@link ISENode}.
    * @param value   The state the Node should be annotated with. True for a "correct" annotation, false for a "false" annotation.
    */
   public static void annotateSETNode(ISENode node, char correctness){
      switch (correctness){
      case 'c': annotateCorrect(node); break;
      case 'f': annotateFalse(node); break; }
   }

   /**
    * annotates the given ISENode with the annotationTypeCorrect annotation
    * @author Peter Schauberger
    */
   public static void annotateCorrect(ISENode node) {
      if(node.getAnnotationLinks(annotationTypeCorrect).length == 0){
         if(node.getAnnotationLinks(annotationTypeFalse).length == 0){
            node.addAnnotationLink(annotationTypeCorrect.createLink(annotationCorrect, node));
         }
         else{
            node.removeAnnotationLink(annotationTypeFalse.createLink(annotationFalse, node));
            node.addAnnotationLink(annotationTypeCorrect.createLink(annotationCorrect, node));
         }
      }
   }

   /**
    * annotates the given ISENode with the annotationTypeFalse annotation
    * @author Peter Schauberger
    */
   public static void annotateFalse(ISENode node) {
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

   /*
    * returns true if the given ISENode has children that are not annotated with the AlgorithmicDebugCorrectAnnotationType
    * @param node the node that should be checked
    */
   public static boolean hasNotCorrectAnnotatedChildren(ISENode node){
      try {
         for(ISENode child : node.getChildren()){
            int len = child.getAnnotationLinks(SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugCorrectAnnotationType.TYPE_ID)).length;
            if(len == 0){
               return true;
            }
         }
      }
      catch (DebugException e) {
         e.printStackTrace();
      }
      return false;
   }

   /*
    * returns true if all children of the given ISENode node are annotated with the AlgorithmicDebugCorrectAnnotationType
    * @param node the node that should be checked
    */
   public static boolean allChildrenAreAnnotatedCorrect(ISENode node){
      boolean ret = true;
      try {
         for(ISENode child : node.getChildren()){
            int len = child.getAnnotationLinks(SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugCorrectAnnotationType.TYPE_ID)).length;
            if(len == 0){
               ret= false;
            }
         }
      }
      catch (DebugException e) {
         e.printStackTrace();
      }
      return ret;
   }
   
   /*
    * annotate the given ISENode with the annotationTypeBug
    * @param node the node that should be annotated
    */
   public static void annotateBug(ISENode node) {

      if(node.getAnnotationLinks(annotationTypeBug).length == 0){
         node.addAnnotationLink(annotationTypeBug.createLink(annotationBug, node));
      }
   }

   /*
    * removes from the given ISENode the annotationTypeCorrect annotation and the annotationTypeFalse annotation. Then annotates the given ISENode with the annotationTypeBug annotation
    */
   public static void annotateBuggy(ISENode node) {
      if(node.getAnnotationLinks(annotationTypeCorrect).length != 0)
         node.removeAnnotationLink(annotationTypeCorrect.createLink(annotationCorrect, node));
      if(node.getAnnotationLinks(annotationTypeFalse).length != 0)
         node.removeAnnotationLink(annotationTypeFalse.createLink(annotationFalse, node));
      node.addAnnotationLink(annotationTypeBug.createLink(annotationBug, node));
   }
}