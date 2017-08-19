package org.key_project.sed.algodebug.searchstrategy2;

import java.util.ArrayList;
import java.util.List;

import org.key_project.sed.algodebug.model2.MethodCall;
import org.key_project.sed.algodebug.util.MCTUtil;
import org.key_project.sed.algodebug.util.SETUtil;

public class SingleStepping extends SearchStrategy implements ISearchStrategy {

   private MethodCall root;

   @Override
   public MethodCall getNext(MethodCall tree) {
      MethodCall call = MCTUtil.getFirstUnMarkedChild(tree);
      if(call == null){
         searchCompletedButNoBugFound = true;
         return null;
         }
         else{
//            for(MethodCall child : )
         }
      return null;
   }

   @Override
   public void markBug(MethodCall methodCall, char correctness) {
      SETUtil.annotateNodesFalseWithoutCalledCalls(methodCall);
   }

   
   public boolean searchBug(MethodCall methodCall) {
      if(methodCall.getCorrectness() == 'f' )
         return true;
      else
         return false;
   }

   @Override
   public void setMethodCallCorrectness(MethodCall methodCall, char correctness) {
      // TODO Auto-generated method stub
      
   }

   @Override
   public boolean treeCompletelySearched() {
      if(root.getCorrectness() == 'c')
         return true;
      else 
         return false;
   }

   @Override
   public void reset() {
      // TODO Auto-generated method stub
      
   }

   @Override
   public boolean bugFound() {
      // TODO Auto-generated method stub
      return false;
   }

   @Override
   public MethodCall getBug() {
      // TODO Auto-generated method stub
      return null;
   }


}