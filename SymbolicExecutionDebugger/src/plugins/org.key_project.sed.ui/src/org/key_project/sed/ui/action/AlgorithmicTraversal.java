package org.key_project.sed.ui.action;

import org.key_project.sed.core.model.ISENode;

public class AlgorithmicTraversal {
   private TraversalStrategy mystrategy = null;

   public void setStrategie(final TraversalStrategy STRATEGY) {
      mystrategy = STRATEGY;
   }

   public ISENode traverse(ISENode node) {
      if (mystrategy != null)
         return mystrategy.algorithm(node);
      else
         return null;
   }
}
