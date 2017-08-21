package org.key_project.sed.algodebug.searchstrategy;

import org.key_project.sed.algodebug.model.MethodCall;
import org.key_project.sed.algodebug.util.MCTUtil;

public class TopDown extends SearchStrategy implements ISearchStrategy {

   private MethodCall lastAskedMethod;
   private MethodCall root;
   /*
    * return null wenn kein nächster Method Call gefunden werden kann
    * -----> weil der Baum komplett abgesucht wurde
    * -----> weil ein Bug gefunden wurde
    * return nächsten abzufragenden Method Call sonst
    */
   @Override
   public MethodCall getNext(MethodCall tree) {
      if(lastAskedMethod == null){
         root = tree;
         lastAskedMethod = tree;
         return tree;
      }
      else if(lastAskedMethod.isRoot() && lastAskedMethod.getCorrectness() == 'c'){
         searchCompletedButNoBugFound = true;
         lastAskedMethod.setMethodCallTreeCompletelySearched(true);
         return null;
      }
      else if(lastAskedMethod.getCorrectness() == 'f' ){
         if(MCTUtil.isEveryChildMarkedAs(lastAskedMethod, 'c')){
            bugFound = true;
            bug = lastAskedMethod;
            return null;
         }
         for(MethodCall child : lastAskedMethod.getListOfCalledMethods()){
            if(child.getCorrectness() == 'u'){
               lastAskedMethod = child;
               return child;
            }
         }
         //Methode inkorrekt und alle Aufrufe korrekt: Methode ist Bug
         bugFound = true;
         bug = lastAskedMethod;
         return null;
      }
      else if(lastAskedMethod.getCorrectness() == 'c'){
         //            SETUtil.annotateMethodCallCorrect(lastAskedMethod);
         if(!lastAskedMethod.isRoot()){
            if(MCTUtil.isEveryChildMarkedAs(lastAskedMethod.getParent(), 'c')){
               bugFound = true;
               bug = lastAskedMethod.getParent();
               return null;
            }
         }
         for(MethodCall sibling : lastAskedMethod.getParent().getListOfCalledMethods()){
            if(sibling.getCorrectness() == 'u'){
               lastAskedMethod = sibling;
               return sibling;
            }
         }
      }
      //kein Bug gefunden
      root.setMethodCallTreeCompletelySearched(true);
      searchCompletedButNoBugFound = true;
      return null;
   }

   public void reset(){
      lastAskedMethod = null;
      root = null;
      searchCompletedButNoBugFound = false;
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
}
