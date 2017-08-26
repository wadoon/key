package org.key_project.sed.algodebug.model;

import java.util.ArrayList;

import org.key_project.sed.core.model.ISENode;

public class Execution {

   /*
    * constructor
    */
   public Execution(ISENode startNode, ISENode EndNode) {
      executionCall = startNode;
      executionReturn = EndNode;
      correctness = 'u';
   }

   /*
    * flag indicating if the exeution is the root element of an execution tree
    */
   private boolean root;

   /*
    * flag indicating if the execution tree was completely searched
    */
   private boolean executionTreeCompletelySearched;

   /*
    * constructor
    */
   public Execution(ISENode start, ISENode ret, ArrayList<Execution> listOfCalledMethods) {
      executionCall = start;
      this.executionReturn = ret;
      this.listOfCalledMethods = listOfCalledMethods;
      correctness = 'u';
   }

   /*
    * set the execution to be the root of an execution tree
    */
   public void setRoot(){
      root = true;
   }

   /*
    * returns true if the execution is the root element of an execution tree
    */
   public boolean isRoot(){
      return root;
   }

   /*
    * returns true if the execution tree is completely searched and no bug was found
    */
   public boolean completelySearched(){
      if(executionTreeCompletelySearched)
         return true;
      else
         return false;
   }

   /*
    * points to the parent of the execution
    */
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

   /*
    * the method call node of the execution
    */
   private ISENode executionCall;

   /*
    * the method return node of the execution
    */
   private ISENode executionReturn;

   /*
    * list of executions that are called from this execution
    */
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

   /*
    * set the execution tree to be completely searched
    */
   public void setExecutionTreeCompletelySearched(boolean b) {
      executionTreeCompletelySearched = b ;
   }

   /*
    * returns true if the execution tree was completely searched
    */
   public boolean getExecutionTreeCompletelySearched(){
      return executionTreeCompletelySearched;
   }
}
