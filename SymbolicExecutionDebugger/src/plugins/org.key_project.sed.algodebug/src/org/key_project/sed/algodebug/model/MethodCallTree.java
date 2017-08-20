package org.key_project.sed.algodebug.model;

import java.util.ArrayList;
import java.util.Collections;

public class MethodCallTree {
   private ArrayList<MethodCall> tree;

   public MethodCallTree(){
      tree = new ArrayList<MethodCall>();
   }

   public MethodCall getMethodCall(int MethodCallIndex){
      if(MethodCallIndex >= 0 && MethodCallIndex < tree.size())
         return tree.get(MethodCallIndex);
      else
         throw new IndexOutOfBoundsException();
   }

   public int getSize(){
      return tree.size();
   }

   public void addCall(MethodCall call){
      if(call != null)
         tree.add(call);
   }

   public void reverseMethodCallTree(){
      Collections.reverse(tree);
   }

   public void setCorrectness(char c){
      for (MethodCall call : tree) {
         call.setMethodCallCorrectness('c');
      }
   }

}
