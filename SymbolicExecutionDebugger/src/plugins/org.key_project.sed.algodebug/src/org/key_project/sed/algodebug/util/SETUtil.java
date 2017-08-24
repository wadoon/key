package org.key_project.sed.algodebug.util;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationType;
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

   public static void highlightNode(ISENode node) {  

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

            return getRoot(node.getParent());}
      }
      catch (DebugException e) {
         // TODO Auto-generated catch block
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
            // TODO Auto-generated catch block
            e.printStackTrace();
         }}
   }

   public static void removeAnnotations(ISENode node){
      registeredAnnotationsFalse = node.getDebugTarget().getRegisteredAnnotations(annotationTypeFalse);
      registeredAnnotationsCorrect = node.getDebugTarget().getRegisteredAnnotations(annotationTypeCorrect);

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
   public static void annotateSETNode(ISENode node, char correctness){
      switch (correctness){
      case 'c': annotateCorrect(node); break;
      case 'f': annotateFalse(node); break; }
   }

   private static ISEAnnotationType annotationTypeCorrect = SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugCorrectAnnotationType.TYPE_ID);
   private static ISEAnnotationType annotationTypeFalse = SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugFalseAnnotationType.TYPE_ID);

   private static ISEAnnotation[] registeredAnnotationsCorrect;
   private static ISEAnnotation[] registeredAnnotationsFalse;

   /**
    * @author Peter Schauberger
    */
   public static void annotateCorrect(ISENode node) {
      registeredAnnotationsCorrect = node.getDebugTarget().getRegisteredAnnotations(annotationTypeCorrect);
      registeredAnnotationsFalse = node.getDebugTarget().getRegisteredAnnotations(annotationTypeFalse);

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

   public static void annotateFalse(ISENode node) {
      //TODO: Hier muss die Annotation erzeugt und registriert werden

      registeredAnnotationsFalse = node.getDebugTarget().getRegisteredAnnotations(annotationTypeFalse);
      registeredAnnotationsCorrect = node.getDebugTarget().getRegisteredAnnotations(annotationTypeCorrect);

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
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
      return false;
   }
}