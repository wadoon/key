package org.key_project.sed.algodebug.model2;

import java.util.ArrayList;

import org.key_project.sed.core.model.ISENode;

public class MethodCall {

   public MethodCall(ISENode startNode, ISENode EndNode) {
      methodCall = startNode;
      methodReturn = EndNode;
      correctness = 'u';
   }

   private boolean root;
   
   private boolean methodCallTreeCompletelySearched;
   
   public MethodCall(ISENode start, ISENode ret, ArrayList<MethodCall> listOfCalledMethods) {
      methodCall = start;
      this.methodReturn = ret;
      this.listOfCalledMethods = listOfCalledMethods;
      correctness = 'u';
   }
   
   public void setRoot(){
      root = true;
   }
   
   public boolean isRoot(){
      return root;
   }
   
   public boolean completelySearched(){
      if(methodCallTreeCompletelySearched)
         return true;
      else
         return false;
   }
   
   private MethodCall parent;
   
   /**
    * @return the parent
    */
   public MethodCall getParent() {
      return parent;
   }

   /**
    * @param parent the parent to set
    */
   public void setParent(MethodCall parent) {
      this.parent = parent;
   }

   private ISENode methodCall;

   private ISENode methodReturn;

   private ArrayList<MethodCall> listOfCalledMethods;
   
   /**
    * @return the listOfCalledCalls
    */
   public ArrayList<MethodCall> getListOfCalledMethods() {
      return listOfCalledMethods;
   }

   /**
    * @param listOfCalledMethods the listOfCalledCalls to set
    */
   public void setListOfCalledMethods(ArrayList<MethodCall> listOfCalledMethods) {
      this.listOfCalledMethods = listOfCalledMethods;
   }

   /**
    * correctness
    * char value - can be 'c' if the ISENode was answered to be correct, or 'f' if it was answered to be false, or 'u' if it was never asked
    */
   private char correctness;

   /**
    * @return the call
    */
   public ISENode getCall() {
      return methodCall;
   } 
   /**
    * @param call the call to set
    */
   public void setCall(ISENode call) {
      this.methodCall = call;
   }
   /**
    * @return the ret
    */
   public ISENode getMethodReturn() {
      return methodReturn;
   }
   /**
    * @param ret the ret to set
    */
   public void setMethodReturn(ISENode ret) {
      this.methodReturn = ret;
   }
   /**
    * @return the correctness
    */
   public char getCorrectness() {
      return correctness;
   }
   /**
    * @param correctness the correctness to set
    */
   public void setMethodCallCorrectness(char correctness) {
      this.correctness = correctness;
   }

   /**
    * @param correctness the correctness to set
    */
   public void setMethodCallCorrectnessIncludingSubMethods(char correctness) {
      this.correctness = correctness;
      for(MethodCall call : listOfCalledMethods){
         call.setMethodCallCorrectnessIncludingSubMethods(correctness);
      }
   }
   /**
    * @param correctness the correctness to set
    */
   public void setMethodCallCorrectnessExcludingSubMethods(char correctness) {
      this.correctness = correctness;}

   public void setMethodCallTreeCompletelySearched(boolean b) {
      methodCallTreeCompletelySearched = b ;
   }
   
   public boolean getMethodCallTreeCompletelySearched(){
      return methodCallTreeCompletelySearched;
   }
}
