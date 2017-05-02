package org.key_project.sed.algodebug.view;

import java.util.Observable;
import java.util.Observer;

import org.eclipse.debug.core.DebugException;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.layout.FormAttachment;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.layout.FormLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.MessageBox;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.wb.swt.SWTResourceManager;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.key_project.sed.algodebug.model.AlgorithmicDebug;
import org.key_project.sed.algodebug.model.Call;
import org.key_project.sed.core.model.ISEConstraint;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.ui.visualization.view.ExecutionTreeView;

public class AlgorithmicDebugView extends ViewPart implements Observer {

   public static final String VIEW_ID = "org.key_project.sed.ui.view.AlgorithmicDebugView";
   
   private ISENode actualNode; 
   private AlgorithmicDebug debug; 
   private Shell shell;
   private Call actualCall;
   
   public AlgorithmicDebugView(){
      debug = new AlgorithmicDebug();
      shell = Display.getCurrent().getActiveShell();
   }
   
   private void showQuestionCall(Call call){
      try {
         debug.unhighlight();
         debug.highlightCall(call);
         methodNameLabel.setText(call.getCall().getName().toString());
         StringBuffer constraintText = new StringBuffer();
         for( ISEConstraint c : call.getRet().getConstraints()){
            constraintText.append("\n"+c.getName());
         }
         constraintsLabel.setText(constraintText.toString());
         returnLabel.setText(call.getRet().getName().toString());
      }
      catch (DebugException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
   }

   private ISENode getSelectedNode(){
      IWorkbench workbench = PlatformUI.getWorkbench();
      
      ISENode selectedNode = null;
      IViewPart part = workbench.getActiveWorkbenchWindow().getActivePage()
            .findView(ExecutionTreeView.VIEW_ID);
        if (part instanceof ExecutionTreeView) {
            ExecutionTreeView view = (ExecutionTreeView) part;
            selectedNode = view.getSelectedNode();
            // now access whatever internals you can get to
        }
        return selectedNode;
   }
   
   Label questionLabel;
   Label methodNameLabel;
   Label constraintsLabel;
   Label returnLabel;
   
   @Override
   public void createPartControl(final Composite parent) {
   
    Display display = Display.getDefault();
    shell = display.getActiveShell();
      
   // create a FormLayout and set its margin
      FormLayout layout = new FormLayout();
      layout.marginHeight = 5;
      layout.marginWidth = 5;
    
      // set layout for parent
      parent.setLayout(layout);
      
      questionLabel = new Label(parent, 0);
      questionLabel.setAlignment(SWT.CENTER);
      questionLabel.setFont(SWTResourceManager.getFont("Segoe UI", 10, SWT.BOLD));
      questionLabel.setText("Is this method doing the right thing?");
      
      FormData fd = new FormData();
      fd.right = new FormAttachment(100, -176);
      fd.left = new FormAttachment(0, 178);
//      fd.bottom = new FormAttachment(0, 20);
      questionLabel.setLayoutData(fd);
     
      methodNameLabel = new Label(parent, 0);
      methodNameLabel.setAlignment(SWT.CENTER);
      methodNameLabel.setFont(SWTResourceManager.getFont("Segoe UI", 12, SWT.BOLD));
//      methodNameLabel.setText("NAME");
      FormData fd2 = new FormData(-1,-1);
      fd2.right = new FormAttachment(100, -18);
      fd2.left = new FormAttachment(0, 10);
      fd2.top = new FormAttachment(questionLabel, 19);
      fd2.bottom = new FormAttachment(100, -339);
//      fd2.bottom = new FormAttachment(0, 10);
      methodNameLabel.setLayoutData(fd2);
      
      constraintsLabel = new Label(parent, 0);
//      constraintsLabel.setText("CONSTRAINTS");
      FormData fd3 = new FormData();
      fd3.right = new FormAttachment(methodNameLabel, 0, SWT.RIGHT);
      fd3.left = new FormAttachment(0, 10);
//      fd3.bottom = new FormAttachment(0, 100);
      constraintsLabel.setLayoutData(fd3);
      
      Button buttonCorrect = new Button(parent, SWT.BORDER);
      fd3.bottom = new FormAttachment(buttonCorrect, -85);
      buttonCorrect.setText("Correct");
      //Display display = parent.getDisplay();
      Color green = display.getSystemColor(SWT.COLOR_GREEN);
      buttonCorrect.setBackground(green);
      
      //TODO: Correct Button
      buttonCorrect.addListener(SWT.Selection, new Listener() {
         public void handleEvent(Event e) {
           switch (e.type) {
           case SWT.Selection:
              if(actualCall == null){
                 MessageBox mb = new MessageBox( parent.getShell());
                 mb.setText("Last call reached!");
                 mb.setMessage("There is no call after this one. No Bug found.");
                 mb.open();
                 break;
                }
              else{
              debug.annotateCall(actualCall, true);
              actualCall = debug.getPath(actualNode).getNextCall();
              if(actualCall != null)
                 showQuestionCall(actualCall);
              else{
                 MessageBox mb = new MessageBox( parent.getShell());
                 mb.setText("Last call reached!");
                 mb.setMessage("There is no call after this one. No Bug found.");
                 mb.open();
                }
              break;
           }}
         }
       });
      
      // create FormData and set each of its sides
      FormData formData1 = new FormData(-1,-1);
      formData1.top = new FormAttachment(0, 390);
      formData1.left = new FormAttachment(0, 80);
    
      // set FormDate for button
      buttonCorrect.setLayoutData(formData1);
      
      //TODO: More Info Button
      // create a button or any other widget
      Button buttonMoreInfo = new Button(parent, SWT.PUSH);
      buttonMoreInfo.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
         }
      });
      formData1.right = new FormAttachment(buttonMoreInfo, -68);
      buttonMoreInfo.setText("More Info");
      buttonMoreInfo.addListener(SWT.Selection, new Listener() {
         public void handleEvent(Event e) {
           switch (e.type) {
           case SWT.Selection:
                
              break;
           }
         }
       });
      
      // create FormData and set each of its sides
      FormData formData = new FormData();
      formData.left = new FormAttachment(0, 251);
      formData.top = new FormAttachment(buttonCorrect, 0, SWT.TOP);
      formData.bottom = new FormAttachment(100, -25);
    
      // set FormDate for button
      buttonMoreInfo.setLayoutData(formData);
    
      //TODO: False Button
      // create a button or any other widget
      Button buttonFalse = new Button(parent, SWT.BORDER);
      formData.right = new FormAttachment(100, -269);
      buttonFalse.setText("False");
      Color red = display.getSystemColor(SWT.COLOR_RED);
      buttonFalse.setBackground(red);
      buttonFalse.addListener(SWT.Selection, new Listener() {
         public void handleEvent(Event e) {
           switch (e.type) {
           case SWT.Selection:
              debug.annotateNode(AlgorithmicDebugView.this.shell, actualNode, false);
              MessageBox mb = new MessageBox(parent.getShell());
              mb.setText("Hint");
              mb.setMessage("Found wrong Method: "+actualNode.toString());
              mb.open();
             break;
           }
         }
       });
    
      // create FormData and set each of its sides
      FormData formData2 = new FormData();
      formData2.top = new FormAttachment(buttonCorrect, 0, SWT.TOP);
      formData2.left = new FormAttachment(buttonMoreInfo, 69);
      formData2.right = new FormAttachment(100, -92);
    
      // set FormDate for button
      buttonFalse.setLayoutData(formData2);
      
      //TODO: Previous Button
      Button btnNewButton = new Button(parent, SWT.NONE);
      btnNewButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            actualCall = debug.getPath(actualNode).getPreviousCall();
            
//            try {
//               System.out.println("Showing previous call from "+actualCall.getCall().getName().toString()+"to" + actualCall.getRet().getName().toString());
//            }
//            catch (DebugException e1) {
//               // TODO Auto-generated catch block
//               e1.printStackTrace();
//            }
            if(actualCall != null)
               showQuestionCall(actualCall);
            else{
             MessageBox mb = new MessageBox( parent.getShell());
             mb.setText("First call reached!");
             mb.setMessage("There is no call before this one.");
             mb.open();
            }
            
         }
      });
      FormData fd_btn_Back = new FormData();
      fd_btn_Back.bottom = new FormAttachment(methodNameLabel, -39);
      fd_btn_Back.top = new FormAttachment(0, 20);
      fd_btn_Back.left = new FormAttachment(0, 10);
      btnNewButton.setLayoutData(fd_btn_Back);
      btnNewButton.setText("Back");
      
      //TODO: Button Next
      Button btnNext = new Button(parent, SWT.NONE);
      btnNext.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            actualCall = debug.getPath(actualNode).getNextCall();
//            try {
//               System.out.println("Showing next call from "+call.getCall().getName().toString()+"to" + call.getRet().getName().toString());
//            }
//            catch (DebugException e1) {
//               // TODO Auto-generated catch block
//               e1.printStackTrace();
//            }
            if(actualCall != null)
               showQuestionCall(actualCall);
            else{
               MessageBox mb = new MessageBox( parent.getShell());
               mb.setText("Last call reached!");
               mb.setMessage("There is no call after this one.");
               mb.open();
            }
         }
      });
      FormData fd_btn_Next = new FormData();
      fd_btn_Next.bottom = new FormAttachment(methodNameLabel, -39);
      fd_btn_Next.top = new FormAttachment(0, 19);
      fd_btn_Next.right = new FormAttachment(100, -10);
      btnNext.setLayoutData(fd_btn_Next);
      btnNext.setText("Next");
      
      //TODO: Start Debugging Button
      Button btnStartAlgorithmicDebugging = new Button(parent, SWT.NONE);
      fd_btn_Back.right = new FormAttachment(100, -465);
      fd.top = new FormAttachment(0, 47);
      fd_btn_Next.left = new FormAttachment(0, 481);
      btnStartAlgorithmicDebugging.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            if(getSelectedNode() != null){
               //System.out.println("STARTKNOTEN: " +getSelectedNode().toString());
                  actualNode = debug.selectNode(getSelectedNode());

                  actualCall = debug.getPath(actualNode).getStartCall();
                if(actualCall != null)
                   showQuestionCall(actualCall);
                }
            }
         }
      );
      FormData fd_btnNewButton_1 = new FormData();
      fd_btnNewButton_1.bottom = new FormAttachment(questionLabel, -6);
      fd_btnNewButton_1.right = new FormAttachment(btnNext, -78);
      fd_btnNewButton_1.left = new FormAttachment(btnNewButton, 76);
      btnStartAlgorithmicDebugging.setLayoutData(fd_btnNewButton_1);
      btnStartAlgorithmicDebugging.setText("Start Algorithmic Debugging");
      
      Label lblConstraintslabel = new Label(parent, SWT.NONE);
      fd3.top = new FormAttachment(lblConstraintslabel, 6);
      lblConstraintslabel.setFont(SWTResourceManager.getFont("Segoe UI", 9, SWT.BOLD));
      FormData fd_lblConstraintslabel = new FormData();
      fd_lblConstraintslabel.top = new FormAttachment(methodNameLabel, 6);
      fd_lblConstraintslabel.left = new FormAttachment(0, 208);
      lblConstraintslabel.setLayoutData(fd_lblConstraintslabel);
      lblConstraintslabel.setText("while using these constraints:");
      
      Label lblReturnlabel = new Label(parent, SWT.NONE);
      lblReturnlabel.setFont(SWTResourceManager.getFont("Segoe UI", 9, SWT.BOLD));
      FormData fd_lblReturnlabel = new FormData();
      fd_lblReturnlabel.top = new FormAttachment(constraintsLabel, 6);
      fd_lblReturnlabel.left = new FormAttachment(0, 233);
      lblReturnlabel.setLayoutData(fd_lblReturnlabel);
      lblReturnlabel.setText("and this return value:");
      
      returnLabel = new Label(parent, SWT.NONE);
      FormData fd_lblReturnvaluelabel = new FormData();
      fd_lblReturnvaluelabel.right = new FormAttachment(methodNameLabel, 0, SWT.RIGHT);
      fd_lblReturnvaluelabel.top = new FormAttachment(lblReturnlabel, 16);
      fd_lblReturnvaluelabel.bottom = new FormAttachment(buttonCorrect, -1);
      fd_lblReturnvaluelabel.left = new FormAttachment(methodNameLabel, 5, SWT.LEFT);
      returnLabel.setLayoutData(fd_lblReturnvaluelabel);
   }

   @Override
   public void setFocus() {
      questionLabel.setFocus();
   }
  
   @Override
   public void update(Observable o, Object arg) {
     
   }
}
