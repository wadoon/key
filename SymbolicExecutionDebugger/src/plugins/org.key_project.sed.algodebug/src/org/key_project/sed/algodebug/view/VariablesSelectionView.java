package org.key_project.sed.algodebug.view;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.swt.widgets.List;
import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.swt.SWT;
import org.key_project.sed.algodebug.provider.ExecutionTreeNodeListContentProvider;
import org.key_project.sed.algodebug.provider.ExecutionTreeNodeListLabelProvider;

public class VariablesSelectionView extends ViewPart {
   
   public static final String VIEW_ID = "org.key_project.sed.ui.view.VariablesSelectionView";
   
   public VariablesSelectionView() {
      // TODO Auto-generated constructor stub
   }

   @Override
   public void createPartControl(Composite parent) {
      
      ListViewer viewer = new ListViewer(parent, SWT.BORDER | SWT.V_SCROLL);
      viewer.setContentProvider(new ExecutionTreeNodeListContentProvider());
      viewer.setLabelProvider(new ExecutionTreeNodeListLabelProvider());
      List list = viewer.getList();
      
   }

   @Override
   public void setFocus() {
      // TODO Auto-generated method stub
   }

}
