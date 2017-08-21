package org.key_project.sed.algodebug.searchstrategy;

import org.key_project.sed.algodebug.model.MethodCall;

public class SingleStepping extends SearchStrategy implements ISearchStrategy {

   private MethodCall root;

   @Override
   public MethodCall getNext(MethodCall tree) {
      if(root == null)
         root = tree;
      switch(tree.getCorrectness()){
      case 'f':{
         bugFound = true;
         bug = tree;
         return null;
      }
      case 'c':{
         root.setMethodCallTreeCompletelySearched(true);
         searchCompletedButNoBugFound = true;
         return null;
      }
      case 'u':{
         for(MethodCall child : tree.getListOfCalledMethods()){
            switch(child.getCorrectness()){
            case 'f':         
               bugFound = true;
               bug = child;
               return null;
            case 'c':
               continue;
            case 'u':
               return getNext(child);
            }
         }
         return tree;
      }
      
      }
      return null;
   }

   @Override
   public void setMethodCallCorrectness(MethodCall methodCall, char correctness) {
      methodCall.setMethodCallCorrectness(correctness);
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
      root = null;
      searchCompletedButNoBugFound = false;
   }
}