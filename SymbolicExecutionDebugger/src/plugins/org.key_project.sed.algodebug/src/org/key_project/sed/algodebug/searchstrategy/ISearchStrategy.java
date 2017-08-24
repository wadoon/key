package org.key_project.sed.algodebug.searchstrategy;

import org.key_project.sed.algodebug.model.Execution;

public interface ISearchStrategy {
   public Execution getNext(Execution executionTree);
   public void setExecutionCorrectness(Execution execution, char correctness);
   public boolean treeCompletelySearched();
   public void reset();
   public boolean bugFound();
   public Execution getBug();
   public boolean searchCompletedButNoBugFound();
}
