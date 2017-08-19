package org.key_project.sed.algodebug.searchstrategy;

import java.util.ArrayList;

import org.key_project.sed.algodebug.model.QuestionPath;
import org.key_project.sed.core.model.ISENode;

public interface ISearchStrategy {
   public ArrayList<QuestionPath> generateCallTree(ISENode root);
}
