package org.key_project.sed.algodebug.model;

import java.util.ArrayList;
import java.util.Collections;

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
   
   public void reversePath(){
      Collections.reverse(path);
   }

   public void setCorrectness(char c){
      for (Call call : path) {
         call.setCorrectness('c');
      }
   }
   
}
