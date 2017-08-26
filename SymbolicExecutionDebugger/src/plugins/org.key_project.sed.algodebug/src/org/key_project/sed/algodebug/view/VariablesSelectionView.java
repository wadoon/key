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

   /*
    * constructor
    */
   public VariablesSelectionView(){
   }

   /*
    * the viewer used to display the list of ISENodes of the SET
    * At this viewer the method call of the actual asked execution is selected
    */
   static ListViewer viewerLeft = null;

   /*
    * the viewer used to display the list of ISENodes of the SET
    * At this viewer the method return of the actual asked execution is selected
    */
   static ListViewer viewerRight = null;

   /*
    * returns the viewer used to display the method call stack
    */
   public static ListViewer getviewerLeft (){
      return viewerLeft;
   }

   /*
    * returns the viewer used to display the method return stack
    */
   public static ListViewer getviewerRight (){
      return viewerRight;
   }

   /*
    * set the content of the viewers
    */
   public void getContent(){
      Object[] NodeArray = null;
      IViewPart part = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().findView("org.key_project.sed.ui.view.AlgorithmicDebugView");
      if (part instanceof AlgorithmicDebugView) {
         AlgorithmicDebugView view = (AlgorithmicDebugView) part;
         NodeArray =  view.getExecutionTreeAsArray();
      }
      if(NodeArray == null){
         viewerLeft.setInput(null);
         viewerRight.setInput(null);
      }
      else{
         viewerLeft.setInput(NodeArray);
         viewerRight.setInput(NodeArray);
      }
   }

   /*
    * set the input of the viewers to null
    */
   public void clear(){
      viewerLeft.setInput(null);
      viewerRight.setInput(null);
   }

   /*
    * IDCProvider: Dummy Provider, needed only as Parameter for variables view
    */
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

   /*
    * the variables views that show the stack
    */
   private IViewPart variablesViewLeft,variablesViewRight;

   /*
    * creates the user interface of the variables selection view
    */
   private void createViews(){
      IWorkbenchPage workbenchpage = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
      try {
         variablesViewLeft = workbenchpage.showView("org.key_project.sed.ui.view.AlgorithmicDebugVariablesView", "VariablesViewLeft",IWorkbenchPage.VIEW_ACTIVATE);
         variablesViewRight = workbenchpage.showView("org.key_project.sed.ui.view.AlgorithmicDebugVariablesView", "VariablesViewRight",IWorkbenchPage.VIEW_ACTIVATE);
      }
      catch (PartInitException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }

      IViewPart VPartLeft = variablesViewLeft;
      final AlgorithmicDebugVariablesView left = (AlgorithmicDebugVariablesView) VPartLeft ;
      viewerLeft.addSelectionChangedListener(new ISelectionChangedListener() {
         @Override
         public void selectionChanged(SelectionChangedEvent event) {
            left.debugContextChanged(new DebugContextEvent( IDCProvider, event.getSelection(), 1)); //warum flags = 1 ?
         }
      });

      IViewPart VPartRight = variablesViewRight;
      final AlgorithmicDebugVariablesView right = (AlgorithmicDebugVariablesView) VPartRight ;
      viewerRight.addSelectionChangedListener(new ISelectionChangedListener() {

         @Override
         public void selectionChanged(SelectionChangedEvent event) {
            right.debugContextChanged(new DebugContextEvent( IDCProvider, event.getSelection(), 1)); //warum flags = 1 ?
         }
      });
   }

/*
 * (non-Javadoc)
 * @see org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets.Composite)
 */
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

   /*
    * (non-Javadoc)
    * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
    */
   @Override
   public void setFocus() {
   }

}
