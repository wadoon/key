package org.key_project.sed.algodebug.util;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.algodebug.model.Execution;
import org.key_project.sed.core.model.ISEBranchCondition;
import org.key_project.sed.core.model.ISEBranchStatement;
import org.key_project.sed.core.model.ISEMethodCall;
import org.key_project.sed.core.model.ISEMethodReturn;
import org.key_project.sed.core.model.ISENode;

public class MCTUtil {

   public static boolean isEveryChildMarkedAs(Execution execution, char correctness){
      for(Execution child : execution.getListOfCalledMethods()){
         if(child.getCorrectness() != correctness)
            return false;
      }
      return true;
   }

   public static void annotateExecutionPartialCorrect(Execution execution, char correctness) {
      ISENode node = execution.getExecutionReturn();
      try {
         while(!node.equals(execution.getCall().getParent()) &&  !(node instanceof ISEBranchStatement && SETUtil.hasNotCorrectAnnotatedChildren(node)) &&!(node instanceof ISEBranchCondition && SETUtil.hasNotCorrectAnnotatedChildren(node)) ){
            SETUtil.annotateCorrect(node);
            node = node.getParent();
         }
      }
      catch (DebugException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
   }

   public static List<ISENode> getListOfExecutionNodes(Execution execution){
      ISENode node = execution.getExecutionReturn();
      List<ISENode> list = new ArrayList<ISENode>();
      try {
         while(!(node.equals(execution.getCall().getParent()))){
            list.add(0, node);
            node = node.getParent();
         }}
      catch (DebugException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
      return list;
   }

   public static void annotateSETNodesOfABuggyExecution(Execution bug) {
      List<ISENode> list = getListOfExecutionNodes(bug);
      int counter = 0;
      int nodeCounter = 1;
      SETUtil.annotateFalse(list.get(0));
      if(list.size() > 1){
      ISENode node = list.get(1);

      while(!node.equals(bug.getExecutionReturn())){
         if(node instanceof ISEMethodCall)
            counter++;
         else if(node instanceof ISEMethodReturn)
            counter--;
         else
            if(counter == 0)
               SETUtil.annotateFalse(node);
         nodeCounter++;
         node = list.get(nodeCounter);
      }
      SETUtil.annotateFalse(list.get(list.size()-1));}
      
   }
}
