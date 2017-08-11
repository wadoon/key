package org.key_project.sed.algodebug.searchstrategy;

import java.util.ArrayList;

import org.key_project.sed.algodebug.model.CallPath;
import org.key_project.sed.core.model.ISENode;

public interface ISearchStrategy {
   public ArrayList<CallPath> generateCallTree(ISENode root);
}
