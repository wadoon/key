package org.key_project.sed.algodebug.model;

import org.key_project.sed.core.model.ISENode;

public class Call {

   public Call(ISENode startNode, ISENode EndNode) {
      call = startNode;
      ret = EndNode;
   }

   private ISENode call;

   private ISENode ret;
   
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
}
