package org.key_project.sed.algodebug.view;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.debug.ui.contexts.DebugContextEvent;
import org.eclipse.debug.ui.contexts.IDebugContextListener;
import org.eclipse.debug.ui.contexts.IDebugContextProvider;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.swt.SWT;
import org.key_project.sed.algodebug.provider.ExecutionTreeNodeListContentProvider;
import org.key_project.sed.algodebug.provider.ExecutionTreeNodeListLabelProvider;
import org.eclipse.swt.custom.SashForm;

@SuppressWarnings("restriction")
public class VariablesSelectionView extends ViewPart {
   
   public static final String VIEW_ID = "org.key_project.sed.ui.view.VariablesSelectionView";
   
   public VariablesSelectionView(){
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

   private final IDebugContextProvider IDCProvider = new IDebugContextProvider() {
      
      @Override
      public void removeDebugContextListener(IDebugContextListener listener) {
      }
      
      @Override
      public IWorkbenchPart getPart() {
         return null;
      }
      
      @Override
      public ISelection getActiveContext() {
         return null;
      }
      
      @Override
      public void addDebugContextListener(IDebugContextListener listener) {      
      }
   };

   private IViewPart variablesViewLeft,variablesViewRight;
   
   private void createViews(){
      IWorkbenchPage workbenchpage = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
      try {
         variablesViewLeft = workbenchpage.showView("org.key_project.sed.ui.view.myVariablesView", "VariablesViewLeft",IWorkbenchPage.VIEW_ACTIVATE);
         variablesViewRight = workbenchpage.showView("org.key_project.sed.ui.view.myVariablesView", "VariablesViewRight",IWorkbenchPage.VIEW_ACTIVATE);
      }
      catch (PartInitException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
      
      IViewPart VPartLeft = variablesViewLeft;
      final AlgoDebugVariablesView left = (AlgoDebugVariablesView) VPartLeft ;
      viewerLeft.addSelectionChangedListener(new ISelectionChangedListener() {
         @Override
         public void selectionChanged(SelectionChangedEvent event) {
            left.debugContextChanged(new DebugContextEvent( IDCProvider, event.getSelection(), 1)); //warum flags = 1 ?
         }
      });
      
      IViewPart VPartRight = variablesViewRight;
      final AlgoDebugVariablesView right = (AlgoDebugVariablesView) VPartRight ;
      viewerRight.addSelectionChangedListener(new ISelectionChangedListener() {
   
         @Override
         public void selectionChanged(SelectionChangedEvent event) {
            right.debugContextChanged(new DebugContextEvent( IDCProvider, event.getSelection(), 1)); //warum flags = 1 ?
         }
      });
   }
   
   
   @Override
      public void createPartControl(Composite parent) {
      
         SashForm sashForm = new SashForm(parent, SWT.NONE);
         
         viewerLeft = new ListViewer(sashForm, SWT.BORDER | SWT.V_SCROLL | SWT.H_SCROLL);
         viewerLeft.setContentProvider(new ExecutionTreeNodeListContentProvider());
         viewerLeft.setLabelProvider(new ExecutionTreeNodeListLabelProvider());
         
         viewerRight = new ListViewer(sashForm, SWT.BORDER | SWT.V_SCROLL | SWT.H_SCROLL);
         viewerRight.setContentProvider(new ExecutionTreeNodeListContentProvider());
         viewerRight.setLabelProvider(new ExecutionTreeNodeListLabelProvider());
         
         sashForm.setWeights(new int[] {1, 1});
         
         createViews();
         getContent();
      }
   
   @Override
   public void setFocus() {
      getContent();
   }
}
