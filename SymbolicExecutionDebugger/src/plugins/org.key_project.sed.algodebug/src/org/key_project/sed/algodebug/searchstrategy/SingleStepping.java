package org.key_project.sed.algodebug.searchstrategy;

import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedList;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.algodebug.model.Call;
import org.key_project.sed.algodebug.model.CallPath;
import org.key_project.sed.core.annotation.impl.AlgorithmicDebugCorrectAnnotationType;
import org.key_project.sed.core.model.ISEBaseMethodReturn;
import org.key_project.sed.core.model.ISEExceptionalMethodReturn;
import org.key_project.sed.core.model.ISEExceptionalTermination;
import org.key_project.sed.core.model.ISEMethodCall;
import org.key_project.sed.core.model.ISEMethodReturn;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.util.SEAnnotationUtil;

public class SingleStepping implements ISearchStrategy {

   public SingleStepping(){
      this.tree = new ArrayList<CallPath>();
   }

   private ArrayList<CallPath> tree;

   @Override
   public ArrayList<CallPath> generateCallTree(ISENode root) {
      return generatePaths(root);
   }

   public ArrayList<CallPath> generatePaths(ISENode node){
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

   private void addPath(ISENode leaf){
      CallPath path = new CallPath();
      ArrayList<ISENode> list = getListOfPathNodes(leaf);
      for(ISENode node : list){
         if(node instanceof ISEMethodReturn || node instanceof ISEExceptionalMethodReturn){
            Deque<ISENode> stack = new LinkedList<ISENode>();
            ISENode temp = null;
            try {
               temp = node.getParent();
            }
            catch (DebugException e1) {
               // TODO Auto-generated catch block
               e1.printStackTrace();
            }
            do{
               if((temp instanceof ISEMethodCall) && stack.isEmpty()){
                  path.addCall(new Call(temp, node));
                  break;}
               else if(temp instanceof ISEMethodReturn)
                  stack.push(temp);
               else if((temp instanceof ISEMethodCall) && !stack.isEmpty())
                  stack.pop();
               else if(temp instanceof ISEMethodCall && stack.isEmpty() ){
                  
               }
               try {
                  temp = temp.getParent();
               }
               catch (DebugException e) {
                  // TODO Auto-generated catch block
                  e.printStackTrace();
               }
            }while(!(temp instanceof ISEThread));
         }

      }
      tree.add(path);
   }

   private ArrayList<ISENode> getListOfPathNodes(ISENode leaf){
      ISENode node = leaf;
      ArrayList<ISENode> list = new ArrayList<ISENode>();
      //      System.out.println("Generiere Pfad-Liste:");
      while(!(node instanceof ISEThread)){
         list.add(0, node);
         try {
            node = node.getParent();
         }
         catch (DebugException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
         }
      }
      return list;
   }
}
