package org.key_project.sed.algodebug.util;

import org.eclipse.debug.core.DebugException;
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

   private static ISEAnnotation myannotationCorrect = annotationTypeCorrect.createAnnotation();
   private static ISEAnnotation myannotationFalse = annotationTypeFalse.createAnnotation();
   private static ISEAnnotation myannotationBug = annotationTypeBug.createAnnotation();
   private static ISEAnnotation myannotationHighlight = annotationTypeHighlight.createAnnotation();

   public static void init(ISENode node){
      ISEDebugTarget target = node.getDebugTarget();

      myannotationCorrect = ArrayUtil.search(registeredAnnotationsCorrect, new IFilter<ISEAnnotation>() {
         @Override
         public boolean select(ISEAnnotation element) {
            return element instanceof AlgorithmicDebugCorrectAnnotation; 
         }
      });
      if (myannotationCorrect == null){
         myannotationCorrect = annotationTypeCorrect.createAnnotation();
         target.registerAnnotation(myannotationCorrect);
      }

      myannotationFalse = ArrayUtil.search(registeredAnnotationsFalse, new IFilter<ISEAnnotation>() {
         @Override
         public boolean select(ISEAnnotation element) {
            return element instanceof AlgorithmicDebugFalseAnnotation; 
         }
      });
      if (myannotationFalse == null){
         myannotationFalse = annotationTypeFalse.createAnnotation();
         target.registerAnnotation(myannotationFalse);
      }

      myannotationBug = ArrayUtil.search(registeredAnnotationsBug, new IFilter<ISEAnnotation>() {
         @Override
         public boolean select(ISEAnnotation element) {
            return element instanceof AlgorithmicDebugBugAnnotation; 
         }
      });
      if (myannotationBug == null){
         myannotationBug = annotationTypeBug.createAnnotation();
         target.registerAnnotation(myannotationBug);
      }

      myannotationHighlight = ArrayUtil.search(registeredAnnotationsHighlight, new IFilter<ISEAnnotation>() {
         @Override
         public boolean select(ISEAnnotation element) {
            return element instanceof HighlightAnnotation; 
         }
      });
      if (myannotationHighlight == null){
         myannotationHighlight = annotationTypeHighlight.createAnnotation();
         target.registerAnnotation(myannotationHighlight);
      }
   }

   public static void highlightNode(ISENode node) {  

      //If AnnotationLink was not found, we create a new one and attach it to the node
      if(node.getAnnotationLinks(annotationTypeHighlight).length == 0){
         node.addAnnotationLink(annotationTypeHighlight.createLink(myannotationHighlight, node));
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

   public static void removeAnnotations(ISENode node){
      if(node.getAnnotationLinks(annotationTypeCorrect).length != 0)
         node.removeAnnotationLink(annotationTypeCorrect.createLink(myannotationCorrect, node));
      if(node.getAnnotationLinks(annotationTypeFalse).length != 0)
         node.removeAnnotationLink(annotationTypeFalse.createLink(myannotationFalse, node));
      if(node.getAnnotationLinks(annotationTypeBug).length != 0)
         node.removeAnnotationLink(annotationTypeBug.createLink(myannotationBug, node));
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
    * @author Peter Schauberger
    */
   public static void annotateCorrect(ISENode node) {
      if(node.getAnnotationLinks(annotationTypeCorrect).length == 0){
         if(node.getAnnotationLinks(annotationTypeFalse).length == 0){
            node.addAnnotationLink(annotationTypeCorrect.createLink(myannotationCorrect, node));
         }
         else{
            node.removeAnnotationLink(annotationTypeFalse.createLink(myannotationFalse, node));
            node.addAnnotationLink(annotationTypeCorrect.createLink(myannotationCorrect, node));
         }
      }
   }

   public static void annotateFalse(ISENode node) {
      if(node.getAnnotationLinks(annotationTypeFalse).length == 0){
         if(myannotationCorrect == null || node.getAnnotationLinks(annotationTypeCorrect).length == 0){
            node.addAnnotationLink(annotationTypeFalse.createLink(myannotationFalse, node));
         }
         else{ 
            node.removeAnnotationLink(annotationTypeCorrect.createLink(myannotationCorrect, node));
            node.addAnnotationLink(annotationTypeFalse.createLink(myannotationFalse, node));
         }
      }
   }

   /*
    * Gibt wahr zurück wenn es Kinder gibt die nicht korrekt annotiert wurden
    */
   public static boolean hasNotCorrectAnnotatedChildren(ISENode node){
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
         e.printStackTrace();
      }
      return false;
   }

   public static void annotateBug(ISENode node) {

      if(node.getAnnotationLinks(annotationTypeBug).length == 0){
         node.addAnnotationLink(annotationTypeBug.createLink(myannotationBug, node));
      }
   }

   public static void annotateBuggy(ISENode node) {
      if(node.getAnnotationLinks(annotationTypeCorrect).length != 0)
         node.removeAnnotationLink(annotationTypeCorrect.createLink(myannotationCorrect, node));
      if(node.getAnnotationLinks(annotationTypeFalse).length != 0)
         node.removeAnnotationLink(annotationTypeFalse.createLink(myannotationFalse, node));
      node.addAnnotationLink(annotationTypeBug.createLink(myannotationBug, node));
   }
}