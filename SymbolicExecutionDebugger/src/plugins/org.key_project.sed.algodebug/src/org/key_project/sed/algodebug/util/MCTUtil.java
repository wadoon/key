package org.key_project.sed.algodebug.util;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.algodebug.model.MethodCall;
import org.key_project.sed.core.model.ISEBranchCondition;
import org.key_project.sed.core.model.ISEBranchStatement;
import org.key_project.sed.core.model.ISEMethodCall;
import org.key_project.sed.core.model.ISEMethodReturn;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEThread;

public class MCTUtil {

   public static boolean isEveryChildMarkedAs(MethodCall methodCall, char correctness){
      for(MethodCall child : methodCall.getListOfCalledMethods()){
         if(child.getCorrectness() != correctness)
            return false;
      }
      return true;
   }

   public static void markCallAndReturnNodesOfAMethodCall(MethodCall methodCall, char correctness){
      SETUtil.annotateSETNode(methodCall.getCall(), correctness);
      SETUtil.annotateSETNode(methodCall.getMethodReturn(), correctness);
   }

   public static void markMethodCallIncludingCalledMethodCalls(MethodCall methodCall, char correctness) {
      methodCall.setMethodCallCorrectness(correctness);
      for(MethodCall calledMethodCall : methodCall.getListOfCalledMethods()){
         markMethodCallIncludingCalledMethodCalls(calledMethodCall, correctness);
      }
   }

   public static void annotateMethodCallPartialCorrect(MethodCall methodCall, char correctness) {
      ISENode node = methodCall.getMethodReturn();
      try {
         while(!node.equals(methodCall.getCall().getParent()) &&  !(node instanceof ISEBranchStatement && SETUtil.hasNotCorrectAnnotatedChildren(node)) &&!(node instanceof ISEBranchCondition && SETUtil.hasNotCorrectAnnotatedChildren(node)) ){
            SETUtil.annotateCorrect(node);
            node = node.getParent();
         }
      }
      catch (DebugException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
   }

   public static void markMethodCall(MethodCall methodCall, char correctness) {
      methodCall.setMethodCallCorrectness(correctness);
   }

   public static MethodCall getFirstUnMarkedChild(MethodCall methodCall){
      for(MethodCall call : methodCall.getListOfCalledMethods()){
         if(call.getCorrectness() == 'u')
            return call;
      }
      return null;
   }

   public static List<ISENode> getListOfMethodCallNodes(MethodCall methodCall){
      ISENode node = methodCall.getMethodReturn();
      List<ISENode> list = new ArrayList<ISENode>();
      try {
         while(!(node.equals(methodCall.getCall().getParent()))){
            list.add(0, node);
            node = node.getParent();
         }}
      catch (DebugException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
      return list;
   }

   public static void annotateSETNodesOfABuggyMethodCall(MethodCall bug) {
      List<ISENode> list = getListOfMethodCallNodes(bug);
      int counter = 0;
      int nodeCounter = 1;
      SETUtil.annotateFalse(list.get(0));
      ISENode node = list.get(1);

      while(!node.equals(bug.getMethodReturn())){
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
      SETUtil.annotateFalse(list.get(list.size()-1));
      
   }
}
