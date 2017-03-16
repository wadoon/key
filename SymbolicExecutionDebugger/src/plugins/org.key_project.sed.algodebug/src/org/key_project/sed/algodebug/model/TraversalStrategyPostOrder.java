package org.key_project.sed.algodebug.model;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugCorrectAnnotationType;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.util.SEAnnotationUtil;

public class TraversalStrategyPostOrder implements TraversalStrategy {

   public ISENode algorithm(ISENode node) {
      return postOrderTraversal(getRoot(node));
   }
   
   /**
    * Method to find the root node of the Symbolic Execution Tree.
    * @param node    The selected {@link ISENode}.
    * @return        The root {@link ISENode}.
    */
   private ISENode getRoot(ISENode node){
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
   
   /**
    * Method to walk the tree and process the leafs before the other nodes.
    * @param node    The selected {@link ISENode}.
    * @return        The next node {@link ISENode} or null if every node was visited.
    */
   private ISENode postOrderTraversal(ISENode node){
      try {
         if(node.hasChildren()){ //Knoten hat Kinder
            for(ISENode child : node.getChildren()){
               ISENode nextchild = postOrderTraversal(child);
               if(nextchild != null)
                  return nextchild;
               }
            }
         if(node.getAnnotationLinks(SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugCorrectAnnotationType.TYPE_ID)).length == 0){ //Knoten bereits korrekt markiert
            return node;
            }
         }
    catch (DebugException e) {
       // TODO Auto-generated catch block
       e.printStackTrace();
    }
       return null;
   }
}
