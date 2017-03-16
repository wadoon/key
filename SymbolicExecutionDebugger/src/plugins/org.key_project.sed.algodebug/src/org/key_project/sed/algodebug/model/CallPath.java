package org.key_project.sed.algodebug.model;

import java.util.ArrayList;

public class CallPath {
   private ArrayList<Call> path;
   
   public CallPath(){
      path = new ArrayList<Call>();     
   }
   
   public Call getCall(int CallIndex){
      if(CallIndex >= 0 && CallIndex < path.size())
         return path.get(CallIndex);
      else
         throw new IndexOutOfBoundsException();
   }
   
   public int getSize(){
      return path.size();
   }
   
   public void addCall(Call call){
      if(call != null)
         path.add(call);
   }

}
