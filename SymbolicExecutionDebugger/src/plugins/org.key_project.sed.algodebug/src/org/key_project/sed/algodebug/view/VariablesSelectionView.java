package org.key_project.sed.algodebug.view;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.ISelectionListener;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.swt.widgets.List;
import org.eclipse.debug.internal.ui.views.variables.VariablesView;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.swt.SWT;
import org.key_project.sed.algodebug.provider.ExecutionTreeNodeListContentProvider;
import org.key_project.sed.algodebug.provider.ExecutionTreeNodeListLabelProvider;
import org.key_project.sed.core.model.ISENode;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.custom.SashForm;

public class VariablesSelectionView extends ViewPart implements ISelectionListener{
   
   public static final String VIEW_ID = "org.key_project.sed.ui.view.VariablesSelectionView";
   
   public VariablesSelectionView() {
      // TODO Auto-generated constructor stub
   }
static ListViewer viewerLeft = null;
static ListViewer viewerRight = null;

public static ListViewer getviewerLeft (){
   return viewerLeft;
}

public static ListViewer getviewerRight (){
   return viewerRight;
}

private void getContent(){
   Object[] NodeArray = null;
   IViewPart part = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().findView("org.key_project.sed.ui.view.AlgorithmicDebugView");
   if (part instanceof AlgorithmicDebugView) {
      AlgorithmicDebugView view = (AlgorithmicDebugView) part;
      NodeArray =  view.getExecutionTreeAsArray();
  }
   if(NodeArray == null){
      viewerLeft.setInput(null);
      viewerLeft.setInput(null);
   }
   else{
      viewerLeft.setInput(NodeArray);
      viewerRight.setInput(NodeArray);
   }
}

@Override
   public void createPartControl(Composite parent) {
      
      SashForm sashForm = new SashForm(parent, SWT.NONE);
      
      viewerLeft = new ListViewer(sashForm, SWT.BORDER | SWT.V_SCROLL | SWT.H_SCROLL);
      List listOfCallNodes = viewerLeft.getList();
      viewerLeft.setContentProvider(new ExecutionTreeNodeListContentProvider());
      viewerLeft.setLabelProvider(new ExecutionTreeNodeListLabelProvider());

      getSite().setSelectionProvider(viewerLeft);
      registerViwererAtVariablesView(viewerLeft);
      
      viewerRight = new ListViewer(sashForm, SWT.BORDER | SWT.V_SCROLL | SWT.H_SCROLL);
      List listOfReturnNodes = viewerRight.getList();
      
            viewerRight.setContentProvider(new ExecutionTreeNodeListContentProvider());
            viewerRight.setLabelProvider(new ExecutionTreeNodeListLabelProvider());
      sashForm.setWeights(new int[] {1, 1});
      
      getContent();
      getViewSite().getPage().addSelectionListener(this);
   }

private void registerViwererAtVariablesView(ListViewer viewer){
   IViewPart part = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().findView(IDebugUIConstants.ID_VARIABLE_VIEW);
   if (part instanceof VariablesView) {
      VariablesView view = (VariablesView) part;
      view.setSelectionProvider(viewer);
   }
   }

@Override
public void selectionChanged(IWorkbenchPart part, ISelection selection) {
 System.out.println("Selection geändert: " +selection.toString());
}

@Override
public void setFocus() {
   // TODO Auto-generated method stub
   getContent();
}
}
