package org.key_project.sed.algodebug.model;

import java.util.ArrayList;
import java.util.Collections;

public class QuestionPath {
   private ArrayList<Question> path;

   public QuestionPath(){
      path = new ArrayList<Question>();
   }

   public Question getCall(int CallIndex){
      if(CallIndex >= 0 && CallIndex < path.size())
         return path.get(CallIndex);
      else
         throw new IndexOutOfBoundsException();
   }

   public int getSize(){
      return path.size();
   }

   public void addCall(Question call){
      if(call != null)
         path.add(call);
   }

   public void reversePath(){
      Collections.reverse(path);
   }

   public void setCorrectness(char c){
      for (Question call : path) {
         call.setCorrectness('c');
      }
   }

}
