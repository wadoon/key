package org.key_project.sed.algodebug.view;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.swt.widgets.List;
import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.swt.SWT;
import org.key_project.sed.algodebug.provider.ExecutionTreeNodeListContentProvider;
import org.key_project.sed.algodebug.provider.ExecutionTreeNodeListLabelProvider;
import org.key_project.sed.core.model.ISENode;

public class VariablesSelectionView extends ViewPart {
   
   public static final String VIEW_ID = "org.key_project.sed.ui.view.VariablesSelectionView";
   
   public VariablesSelectionView() {
      // TODO Auto-generated constructor stub
   }
ListViewer viewer = null;

public ListViewer getviewer (){
   return viewer;
}

@Override
   public void createPartControl(Composite parent) {
      
      viewer = new ListViewer(parent, SWT.BORDER | SWT.V_SCROLL);
      viewer.setContentProvider(new ExecutionTreeNodeListContentProvider());
      viewer.setLabelProvider(new ExecutionTreeNodeListLabelProvider());
      
      Object[] NodeArray = null;
      IViewPart part = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().findView("org.key_project.sed.ui.view.AlgorithmicDebugView");
      if (part instanceof AlgorithmicDebugView) {
         AlgorithmicDebugView view = (AlgorithmicDebugView) part;
         NodeArray =  view.getExecutionTreeAsArray();
     }
      if(NodeArray == null)
         viewer.setInput(null);
      else
         viewer.setInput(NodeArray);
      //List list = viewer.getList();
      
   }

   @Override
   public void setFocus() {
      // TODO Auto-generated method stub
   }

}
