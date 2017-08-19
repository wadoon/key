package org.key_project.sed.algodebug.searchstrategy;

import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedList;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.algodebug.model.Question;
import org.key_project.sed.algodebug.model.QuestionPath;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugCorrectAnnotationType;
import org.key_project.sed.core.model.ISEBaseMethodReturn;
import org.key_project.sed.core.model.ISEExceptionalMethodReturn;
import org.key_project.sed.core.model.ISEExceptionalTermination;
import org.key_project.sed.core.model.ISEMethodCall;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.util.SEAnnotationUtil;

public class BottomUp implements ISearchStrategy {

   public BottomUp(){
      this.tree = new ArrayList<QuestionPath>();
   }

   private ArrayList<QuestionPath> tree;

   @Override
   public ArrayList<QuestionPath> generateCallTree(ISENode root) {
      return generatePaths(root);
   }


   public ArrayList<QuestionPath> generatePaths(ISENode node){
      try {
         //System.out.println("Generating Paths");
         if(!node.hasChildren()) { //Bei einem Blatt angekommen
            addPath(node);
         }
         else{
            for(ISENode child : node.getChildren()){ //Es gibt Kind-Knoten: Für jeden neuen Pfad hinzufügen
               generatePaths(child);
            }
         }
         return tree;
      }
      catch (DebugException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
      return null;
   }

   /*
    * Erzeugt einen Path indem es von einem Blatt zur Wurzel läuft
    * @author Peter Schauberger
    */
   private void addPath(ISENode leaf){
      try {
         ISENode node = leaf;
         QuestionPath path = new QuestionPath();
         Deque<ISENode> deque = new LinkedList<ISENode>();
         ISENode exception = null;

         if(leaf instanceof ISEExceptionalTermination)
            exception = leaf;

         while(!(node instanceof ISEThread)){
            if(node instanceof ISEBaseMethodReturn){
               deque.push(node);
               //System.out.println("Pushing"+node.getName());
            }
            else if(node instanceof ISEMethodCall){
               //System.out.println("Adding Call: From "+node.getName() + "to"+deque.peekFirst().getName());
               if( deque.isEmpty() && exception != null )
                  path.addCall(new Question(node, exception));
               else if(!( deque.peekFirst() instanceof ISEExceptionalMethodReturn))
                  path.addCall(new Question(node, deque.pop()));
               else
                  path.addCall(new Question(node, deque.peekFirst()));
            }
            node = node.getParent();
         }

         tree.add(path);

      }
      catch (DebugException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
   }
}
