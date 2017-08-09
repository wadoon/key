package org.key_project.sed.algodebug.view;

import java.util.ArrayList;
import java.util.Observable;
import java.util.Observer;
import org.eclipse.core.runtime.ListenerList;
import org.eclipse.debug.core.DebugException;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
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
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.wb.swt.SWTResourceManager;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.key_project.sed.algodebug.model.AlgorithmicDebug;
import org.key_project.sed.algodebug.model.Call;
import org.key_project.sed.core.model.ISEConstraint;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.eclipse.swt.custom.ScrolledComposite;
import org.eclipse.swt.widgets.Combo;

public class AlgorithmicDebugView extends ViewPart implements Observer, ISelectionProvider{

   public static final String VIEW_ID = "org.key_project.sed.ui.view.AlgorithmicDebugView";

   private ISENode actualNode, root; 
   private AlgorithmicDebug debug; 
   private Call actualCall;
   private ListenerList listeners = new ListenerList();

   public AlgorithmicDebugView(){
      debug = new AlgorithmicDebug();
   }

   private void reset(){
      debug.unhighlight();
      debug.removeAllAlgoDebugAnnotations(root);
      debug = new AlgorithmicDebug();
      actualCall = null;
   }

   public void dispose(){
      debug.unhighlight();
      debug.removeAllAlgoDebugAnnotations(root);
      actualNode = null;
      debug = null;
      actualCall = null;
      super.dispose();
   }

   private void showQuestionCall(Call call){
      try {
         //System.out.println("Showing Return: " + call.getRet().getName().toString());
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

   /*
    * getSelectedNode
    * @returns the actual selected node at the {@link ExecutionTreeView}
    */

   private ISENode getSelectedNode(){
      return (KeySEDUtil.getSelectedDebugElement() instanceof ISENode ) ? (ISENode) KeySEDUtil.getSelectedDebugElement() : null;
   }

   Label questionLabel, methodNameLabel, constraintsLabel, returnLabel;
   Combo combo;

   IWorkbenchPage workbenchpage = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();

   @Override
   public void createPartControl(final Composite parent) {

      Display display = Display.getDefault();

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

      Button buttonCorrect = new Button(parent, SWT.BORDER);
      buttonCorrect.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
         }
      });
      buttonCorrect.setText("Correct");
      //Display display = parent.getDisplay();
      Color green = display.getSystemColor(SWT.COLOR_GREEN);
      buttonCorrect.setBackground(green);

      //Correct Button
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

                  //              while(actualCall.getCorrectness() == 'c')
                  actualCall = debug.getCallTree().getNextCall();
                  if(actualCall != null){
                     showQuestionCall(actualCall);
                     setVariablesSelectionViewSelection();}
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

      // set FormDate for button
      FormData fd_buttonCorrect = new FormData(-1,-1);
      fd_buttonCorrect.right = new FormAttachment(0, 207);
      fd_buttonCorrect.left = new FormAttachment(0, 106);
      buttonCorrect.setLayoutData(fd_buttonCorrect);

      //False Button
      // create a button or any other widget
      Button buttonFalse = new Button(parent, SWT.BORDER);
      buttonFalse.setText("False");
      Color red = display.getSystemColor(SWT.COLOR_RED);
      buttonFalse.setBackground(red);

      buttonFalse.addListener(SWT.Selection, new Listener() {
         public void handleEvent(Event e) {
            switch (e.type) {
            case SWT.Selection:
               debug.annotateCallFalse(actualCall);

               MessageBox mb = new MessageBox( parent.getShell());
               mb.setText("Hint!");
               try {
                  mb.setMessage("Found wrong Method: "+actualCall.getCall().getName().toString());
               }
               catch (DebugException e1) {
                  // TODO Auto-generated catch block
                  e1.printStackTrace();
               }
               mb.open();
               break;
            }
         }
      });

      // set FormDate for button
      FormData fd_buttonFalse = new FormData();
      fd_buttonFalse.top = new FormAttachment(buttonCorrect, 0, SWT.TOP);
      fd_buttonFalse.right = new FormAttachment(100, -128);
      fd_buttonFalse.left = new FormAttachment(100, -229);
      buttonFalse.setLayoutData(fd_buttonFalse);

      //Previous Button
      Button btnNewButton = new Button(parent, SWT.NONE);
      btnNewButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            actualCall = debug.getCallTree().getPreviousCall();
            if(actualCall != null){
               showQuestionCall(actualCall);
               setVariablesSelectionViewSelection();
            }
            else{
               MessageBox mb = new MessageBox( parent.getShell());
               mb.setText("First call reached!");
               mb.setMessage("There is no call before this one.");
               mb.open();
            }

         }
      });
      FormData fd_btn_Back = new FormData();
      fd_btn_Back.left = new FormAttachment(0, 10);
      btnNewButton.setLayoutData(fd_btn_Back);
      btnNewButton.setText("Back");

      //Button Next
      Button btnNext = new Button(parent, SWT.NONE);

      btnNext.addSelectionListener(new SelectionAdapter() {

         @Override
         public void widgetSelected(SelectionEvent e) {
            actualCall = debug.getCallTree().getNextCall();
            if(actualCall != null){
               showQuestionCall(actualCall);
               // SWTUtil.select(((org.key_project.sed.ui.visualization.view.ExecutionTreeView)executiontreeView).getDebugView().getViewer(),new StructuredSelection(actualCall.getCall()), true);
               setVariablesSelectionViewSelection();
            }
            else{
               MessageBox mb = new MessageBox( parent.getShell());
               mb.setText("Last call reached!");
               mb.setMessage("There is no call after this one.");
               mb.open();
            }
         }
      });
      FormData fd_btn_Next = new FormData();
      fd_btn_Next.bottom = new FormAttachment(methodNameLabel, -42);
      fd_btn_Next.top = new FormAttachment(btnNewButton, 0, SWT.TOP);
      fd_btn_Next.right = new FormAttachment(100, -10);
      btnNext.setLayoutData(fd_btn_Next);
      btnNext.setText("Next");

      // Start Debugging Button
      final Button btnStart = new Button(parent, SWT.NONE);
      fd_btn_Back.top = new FormAttachment(btnStart, 0, SWT.TOP);
      fd_btn_Back.right = new FormAttachment(100, -456);
      fd.top = new FormAttachment(0, 47);
      fd_btn_Next.left = new FormAttachment(0, 473);
      btnStart.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            if(btnStart.getText().equals("Start")){
               btnStart.setText("Reset");
               actualNode = getSelectedNode();                   //actualNode = debug.selectNode(getSelectedNode()); geändert: warum wurde der erste nicht markierte Node gesucht ??
               root = debug.getRoot(actualNode);
               if(actualNode != null){
                  //System.out.println("STARTKNOTEN: " +getSelectedNode().toString());
                  actualCall = debug.getCallTree(actualNode, combo.getText()).getStartCall();
                  if(actualCall != null){
                     showQuestionCall(actualCall);
                     setVariablesSelectionViewSelection();
                  }
               }
            }
            else if(btnStart.getText().equals("Reset")){
               debug.unhighlight();
               reset();
               actualNode = getSelectedNode();                   //actualNode = debug.selectNode(getSelectedNode()); geändert: warum wurde der erste nicht markierte Node gesucht ??
               if(actualNode != null){
                  //System.out.println("STARTKNOTEN: " +getSelectedNode().toString());
                  actualCall = debug.getCallTree(actualNode, combo.getText()).getStartCall();
                  if(actualCall != null){
                     showQuestionCall(actualCall);
                     setVariablesSelectionViewSelection();
                  }
               }
            }
         }

      }
            );
      FormData fd_btnNewButton_1 = new FormData();
      fd_btnNewButton_1.left = new FormAttachment(btnNewButton, 39);
      fd_btnNewButton_1.bottom = new FormAttachment(questionLabel, -6);
      btnStart.setLayoutData(fd_btnNewButton_1);
      btnStart.setText("Start");

      Label lblConstraintslabel = new Label(parent, SWT.NONE);
      lblConstraintslabel.setFont(SWTResourceManager.getFont("Segoe UI", 9, SWT.BOLD));
      FormData fd_lblConstraintslabel = new FormData();
      fd_lblConstraintslabel.top = new FormAttachment(methodNameLabel, 6);
      fd_lblConstraintslabel.left = new FormAttachment(0, 208);
      lblConstraintslabel.setLayoutData(fd_lblConstraintslabel);
      lblConstraintslabel.setText("while using these constraints:");

      Label lblReturnlabel = new Label(parent, SWT.NONE);
      lblReturnlabel.setFont(SWTResourceManager.getFont("Segoe UI", 9, SWT.BOLD));
      FormData fd_lblReturnlabel = new FormData();
      fd_lblReturnlabel.top = new FormAttachment(0, 311);
      fd_lblReturnlabel.left = new FormAttachment(0, 233);
      lblReturnlabel.setLayoutData(fd_lblReturnlabel);
      lblReturnlabel.setText("and this return value:");

      returnLabel = new Label(parent, SWT.NONE);
      fd_lblReturnlabel.bottom = new FormAttachment(returnLabel, -14);
      fd_buttonCorrect.top = new FormAttachment(returnLabel, 6);
      FormData fd_lblReturnvaluelabel = new FormData();
      fd_lblReturnvaluelabel.top = new FormAttachment(0, 342);
      fd_lblReturnvaluelabel.bottom = new FormAttachment(100, -70);
      fd_lblReturnvaluelabel.right = new FormAttachment(methodNameLabel, 0, SWT.RIGHT);
      fd_lblReturnvaluelabel.left = new FormAttachment(methodNameLabel, 5, SWT.LEFT);
      returnLabel.setLayoutData(fd_lblReturnvaluelabel);

      ScrolledComposite scrolledComposite = new ScrolledComposite(parent, SWT.BORDER | SWT.H_SCROLL | SWT.V_SCROLL);
      FormData fd_scrolledComposite = new FormData();
      fd_scrolledComposite.bottom = new FormAttachment(lblReturnlabel, -16);
      fd_scrolledComposite.top = new FormAttachment(lblConstraintslabel, 8);
      fd_scrolledComposite.right = new FormAttachment(methodNameLabel, 0, SWT.RIGHT);
      fd_scrolledComposite.left = new FormAttachment(returnLabel, 0, SWT.LEFT);
      scrolledComposite.setLayoutData(fd_scrolledComposite);
      scrolledComposite.setExpandHorizontal(true);
      scrolledComposite.setExpandVertical(true);
      scrolledComposite.setMinSize( 50, 50 );


      constraintsLabel = new Label(scrolledComposite, SWT.NONE);
      constraintsLabel.setLayoutData(new FormData());
      scrolledComposite.setContent( constraintsLabel );

      combo = new Combo(parent, SWT.NONE);
      fd_btnNewButton_1.right = new FormAttachment(100, -313);
      FormData fd_combo = new FormData();
      fd_combo.top = new FormAttachment(btnNewButton, 2, SWT.TOP);
      fd_combo.right = new FormAttachment(questionLabel, 0, SWT.RIGHT);
      combo.setLayoutData(fd_combo);
      combo.setText("choose strategy");
      String[] items = { "Bottom Up", "Top Down" };
      combo.setItems(items);
      combo.select(0);
   }

   /*
    * Alle Knoten des Execution Tree in Preorder Reihenfolge in einem Array zurückgeben...
    */
   public Object[] getExecutionTreeAsArray(){
      ISENode root = null;
      if(actualNode != null){
         root = debug.getRoot(actualNode);
      }
      Object[] array = null;
      if(root != null)
         array =  asList(root).toArray();
      return array;
   }

   private void setVariablesSelectionViewSelection() {
      SWTUtil.select(VariablesSelectionView.getviewerLeft(),
            new StructuredSelection(actualCall.getCall()), true);
      SWTUtil.select(VariablesSelectionView.getviewerRight(),
            new StructuredSelection(actualCall.getRet()), true);
   }

   /*
    * asList - Gibt eine Liste mit allen Knoten des ExecutionTree zurück
    */
   private ArrayList<ISENode> asList(ISENode node){
      ArrayList<ISENode> list = new ArrayList<ISENode>();
      list.add(node);
      try {
         if(node.hasChildren()){
            for(ISENode child : node.getChildren()){
               list.addAll(asList(child));
            }
         }
      }
      catch (DebugException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
      return list;
   }

   @Override
   public void setFocus() {
      questionLabel.setFocus();
   }

   @Override
   public void update(Observable o, Object arg) {

   }

   @Override
   public void addSelectionChangedListener(ISelectionChangedListener listener) {
      //System.out.println("Add Listener "+listener.toString());
      listeners.add(listener);        
   }

   @Override
   public ISelection getSelection() {

      if(actualCall != null && actualCall.getCall() != null) {
         // System.out.println("getSelection()");
         ISENode node = actualCall.getCall();
         ISelection selection = new StructuredSelection(node);
         return selection;
      } else {
         return StructuredSelection.EMPTY;
      }
   }

   @Override
   public void removeSelectionChangedListener(ISelectionChangedListener listener) {
      listeners.remove(listener);        
   }

   @Override
   public void setSelection(ISelection selection) {
      Object[] list = listeners.getListeners();
      for (int i = 0; i < list.length; i++) {
         ((ISelectionChangedListener) list[i])
         .selectionChanged(new SelectionChangedEvent(this, selection));
      }
   }

}
