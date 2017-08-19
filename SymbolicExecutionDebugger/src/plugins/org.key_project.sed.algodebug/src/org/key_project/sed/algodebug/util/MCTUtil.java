package org.key_project.sed.algodebug.util;

import org.key_project.sed.algodebug.model2.MethodCall;

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
   
}
