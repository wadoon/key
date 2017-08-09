package org.key_project.sed.algodebug.model;

import org.key_project.sed.core.model.ISENode;

public class Call {

   public Call(ISENode startNode, ISENode EndNode) {
      call = startNode;
      ret = EndNode;
      correctness = 'u';
   }

   private ISENode call;

   private ISENode ret;

   /**
    * correctness
    * char value - can be 'c' if the ISENode was answered to be correct, or 'f' if it was answered to be false, or 'u' if it was never asked
    */
   private char correctness;

   /**
    * @return the call
    */
   public ISENode getCall() {
      return call;
   }
   /**
    * @param call the call to set
    */
   public void setCall(ISENode call) {
      this.call = call;
   }
   /**
    * @return the ret
    */
   public ISENode getRet() {
      return ret;
   }
   /**
    * @param ret the ret to set
    */
   public void setRet(ISENode ret) {
      this.ret = ret;
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
   public void setCorrectness(char correctness) {
      this.correctness = correctness;
   }

}
