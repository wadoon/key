package org.key_project.sed.algodebug.searchstrategy;

import org.key_project.sed.algodebug.model.MethodCall;

public interface ISearchStrategy {
   public MethodCall getNext(MethodCall tree);
   public void setMethodCallCorrectness(MethodCall methodCall, char correctness);
   public boolean treeCompletelySearched();
   public void reset();
   public boolean bugFound();
   public MethodCall getBug();
   public boolean searchCompletedButNoBugFound();
}
