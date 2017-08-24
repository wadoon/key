package org.key_project.sed.algodebug.model;

import java.util.ArrayList;

import org.key_project.sed.core.model.ISENode;

public class Execution {

   public Execution(ISENode startNode, ISENode EndNode) {
      executionCall = startNode;
      executionReturn = EndNode;
      correctness = 'u';
   }

   private boolean root;

   private boolean executionTreeCompletelySearched;

   public Execution(ISENode start, ISENode ret, ArrayList<Execution> listOfCalledMethods) {
      executionCall = start;
      this.executionReturn = ret;
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
      if(executionTreeCompletelySearched)
         return true;
      else
         return false;
   }

   private Execution parent;

   /**
    * @return the parent
    */
   public Execution getParent() {
      return parent;
   }

   /**
    * @param parent the parent to set
    */
   public void setParent(Execution parent) {
      this.parent = parent;
   }

   private ISENode executionCall;

   private ISENode executionReturn;

   private ArrayList<Execution> listOfCalledMethods;

   /**
    * @return the listOfCalledCalls
    */
   public ArrayList<Execution> getListOfCalledMethods() {
      return listOfCalledMethods;
   }

   /**
    * @param listOfCalledMethods the listOfCalledCalls to set
    */
   public void setListOfCalledMethods(ArrayList<Execution> listOfCalledMethods) {
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
      return executionCall;
   } 
   /**
    * @param call the call to set
    */
   public void setCall(ISENode call) {
      this.executionCall = call;
   }
   /**
    * @return the ret
    */
   public ISENode getExecutionReturn() {
      return executionReturn;
   }
   /**
    * @param ret the ret to set
    */
   public void setMethodReturn(ISENode ret) {
      this.executionReturn = ret;
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
   public void setExecutionCorrectness(char correctness) {
      this.correctness = correctness;
   }

   /**
    * @param correctness the correctness to set
    */
   public void setExecutionCorrectnessIncludingSubMethods(char correctness) {
      this.correctness = correctness;
      for(Execution call : listOfCalledMethods){
         call.setExecutionCorrectnessIncludingSubMethods(correctness);
      }
   }
   /**
    * @param correctness the correctness to set
    */
   public void setMethodCallCorrectnessExcludingSubMethods(char correctness) {
      this.correctness = correctness;}

   public void setExecutionTreeCompletelySearched(boolean b) {
      executionTreeCompletelySearched = b ;
   }

   public boolean getExecutionTreeCompletelySearched(){
      return executionTreeCompletelySearched;
   }
}
