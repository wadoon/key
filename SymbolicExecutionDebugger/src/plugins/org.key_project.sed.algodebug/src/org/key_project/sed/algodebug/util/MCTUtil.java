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

   /*
    * returns true if every child of the given execution is annotated with the given correctness
    */
   public static boolean isEveryChildMarkedAs(Execution execution, char correctness){
      for(Execution child : execution.getListOfCalledMethods()){
         if(child.getCorrectness() != correctness)
            return false;
      }
      return true;
   }

   /*
    * annotates the ISENodes of the given execution correct backwards until a branch is reached that has a child that is not annotated to be correct
    */
   public static void annotateExecutionPartialCorrect(Execution execution) {
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

   /*
    * returns a list of all ISENodes of the given execution
    * @return the list
    */
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

   /*
    * annotates the ISENodes of a buggy execution with the abbotationBug annotation
    * @param bug the execution that has to be annotated
    */
   public static void annotateSETNodesOfABuggyExecution(Execution bug) {
      List<ISENode> list = getListOfExecutionNodes(bug);
      int counter = 0;
      int nodeCounter = 1;
      SETUtil.annotateBuggy(list.get(0));
      if(list.size() > 1){
         ISENode node = list.get(1);

         while(!node.equals(bug.getExecutionReturn())){
            if(node instanceof ISEMethodCall)
               counter++;
            else if(node instanceof ISEMethodReturn)
               counter--;
            else
               if(counter == 0)
                  SETUtil.annotateBuggy(node);
            nodeCounter++;
            node = list.get(nodeCounter);
         }
         SETUtil.annotateBuggy(list.get(list.size()-1));
      }

   }

   /*
    * annotates the ISENodes of the given execution but does not annotate the called executions
    * @param execution the execution that is the root for this annotation process
    * @param correctness the correctness used to annotate the ISENodes
    */
   public static void annotateSETNodesOfExecutionExcludingSubExecutions(Execution execution, char correctness) {
      List<ISENode> list = getListOfExecutionNodes(execution);
      int counter = 0;
      int nodeCounter = 1;
      switch(correctness){
      case 'c':      SETUtil.annotateCorrect(list.get(0));break;
      case 'f':      SETUtil.annotateFalse(list.get(0));break;
      }
      if(list.size() > 1){
         ISENode node = list.get(1);

         while(!node.equals(execution.getExecutionReturn())){
            if(node instanceof ISEMethodCall)
               counter++;
            else if(node instanceof ISEMethodReturn)
               counter--;
            else
               if(counter == 0)
                  switch(correctness){
                  case 'c':      SETUtil.annotateCorrect(node);break;
                  case 'f':      SETUtil.annotateFalse(node);break;
                  }
            nodeCounter++;
            node = list.get(nodeCounter);
         }
         switch(correctness){
         case 'c':      SETUtil.annotateCorrect(list.get(list.size()-1));break;
         case 'f':      SETUtil.annotateFalse(list.get(list.size()-1));break;
         }
      }
   }

   /*
    * annotates the execution itself and every child exeution down to the leafs with the correctness given as parameter
    * @param execution the execution that is the root for this annotation process
    * @param correctness the correctness used to annotate the ISENodes
    */
   public static void annotateExecutionRecursively(Execution execution, char correctness) {
      annotateSETNodesOfExecutionExcludingSubExecutions(execution,correctness);
      for(Execution child : execution.getListOfCalledMethods()){
         annotateExecutionRecursively(child, correctness);
      }
   }
}
