package org.key_project.sed.algodebug.view;

import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.SWT;

public class SelectionTest extends ViewPart {

   public SelectionTest() {
      // TODO Auto-generated constructor stub
   }
   private IViewPart variablesSelectionView,variablesView;
   @Override
   public void createPartControl(Composite parent) {
      

      final Label lblLabel = new Label(parent, SWT.NONE);
      lblLabel.setText("label");
      IWorkbenchPage workbenchpage = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
      try {
         variablesSelectionView = workbenchpage.showView("org.key_project.sed.ui.view.VariablesSelectionView", null, IWorkbenchPage.VIEW_ACTIVATE);
        // variablesView = workbenchpage.showView("org.key_project.sed.ui.view.myVariablesView");
      }
      catch (PartInitException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
      
//      IViewPart VPart = variablesView;
//      final myVariablesView sw = (myVariablesView) VPart ;
////      if (VPart instanceof myVariablesView) {
////         sw = (myVariablesView) VPart;
////      }
//      
//      ListViewer viewer = VariablesSelectionView.getviewerLeft();
//      viewer.addSelectionChangedListener(new ISelectionChangedListener() {
//         
//         @Override
//         public void selectionChanged(SelectionChangedEvent event) {
//            String selection = "";
//            selection = event.getSelection().toString();
//            lblLabel.setText(selection);
//            
//            //sw.getSelectionProviderWrapper().setSelection(new StructuredSelection(event.getSelection())); 
//            //getSelectionProviderWrapper().setSelection(event.getSelection());
//         }
//      });

   }
   
   @Override
   public void setFocus() {
      // TODO Auto-generated method stub
      
   }

}
