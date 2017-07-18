package org.key_project.sed.algodebug.provider;

import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.PlatformUI;
import org.key_project.sed.algodebug.view.AlgorithmicDebugView;
import org.key_project.sed.core.model.ISENode;

public class ExecutionTreeNodeListContentProvider implements IStructuredContentProvider{

   public ExecutionTreeNodeListContentProvider() {
   }

   @Override
   public void dispose() {      
   }

   @Override
   public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {      
   }

   @Override
   public Object[] getElements(Object inputElement) {
      //TODO: Alle Nodes des Execution Tree als Liste zurückgeben...
      ISENode[] NodeArray = null;
      IViewPart part = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().findView("org.key_project.sed.ui.view.AlgorithmicDebugView");
      if (part instanceof AlgorithmicDebugView) {
         AlgorithmicDebugView view = (AlgorithmicDebugView) part;
         NodeArray =  view.getExecutionTreeAsArray();
     }
      
      return NodeArray != null ? NodeArray : null;
   }

}
