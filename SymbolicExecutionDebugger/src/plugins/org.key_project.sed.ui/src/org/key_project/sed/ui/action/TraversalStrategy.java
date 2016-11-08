package org.key_project.sed.ui.action;

import org.key_project.sed.core.model.ISENode;

public interface TraversalStrategy {
   ISENode algorithm(ISENode node);
}
