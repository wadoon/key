package org.key_project.sed.algodebug.model;

import org.eclipse.debug.core.DebugException;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.algodebug.LinkAction.AlgorithmicDebugCorrectAnnotationLinkAction;
import org.key_project.sed.algodebug.LinkAction.AlgorithmicDebugFalseAnnotationLinkAction;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugCorrectAnnotationType;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.util.SEAnnotationUtil;

/**
 * @author Peter Schauberger
 */
public class AlgorithmicDebug  {
   
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
      
      while(  !(node instanceof ISEThread)){
         if(node == call.getCall()){
            annotateNode(shell, node, bool); //annotieren
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
   
   /*
    * Gibt wahr zurück wenn es Kinder gibt die nicht korrekt annotiert wurden
    */
   private boolean hasUnAnnotatedChildren(ISENode node){
      try {
         for(ISENode child : node.getChildren()){
            if(node.getAnnotationLinks(SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugCorrectAnnotationType.TYPE_ID)).length == 0){ //Knoten bereits korrekt markiert
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