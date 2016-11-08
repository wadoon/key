package org.key_project.sed.ui.action;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugCorrectAnnotationType;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.util.SEAnnotationUtil;

public class TraversalStrategyPreOrder implements TraversalStrategy {

   public ISENode algorithm(ISENode node) {
      return preOrderTraversal(getRoot(node));
   }
   
   /**
    * Method to find the root node of the Symbolic Execution Tree.
    * @param node    The selected {@link ISENode}.
    * @return        The root {@link ISENode}.
    */
   private ISENode getRoot(ISENode node){
      try {
         if( node.getParent() instanceof ISEThread)
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
    * Method to walk the tree in preorder sequence
    * @param node    The selected {@link ISENode}.
    * @return        The next node {@link ISENode} or null if every node was visited.
    */
   private ISENode preOrderTraversal(ISENode node){
      try {
       if(node.getAnnotationLinks(SEAnnotationUtil.getAnnotationtype(AlgorithmicDebugCorrectAnnotationType.TYPE_ID)).length == 0)
          return node;
             else{
                if(node.hasChildren()){
                   for(ISENode child : node.getChildren()){
                      ISENode nextchild = preOrderTraversal(child);
                      if(nextchild != null)
                         return nextchild;
                      }
                }
                else
                   return null;
             }
       }
    catch (DebugException e) {
       // TODO Auto-generated catch block
       e.printStackTrace();
    }
       return null;
   }

}
