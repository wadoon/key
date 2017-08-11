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
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.MessageBox;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.key_project.sed.algodebug.model.AlgorithmicDebug;
import org.key_project.sed.algodebug.model.Call;
import org.key_project.sed.core.model.ISEConstraint;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Text;

@SuppressWarnings("unused")
public class AlgorithmicDebugView extends ViewPart implements Observer, ISelectionProvider{

   public static final String VIEW_ID = "org.key_project.sed.ui.view.AlgorithmicDebugView";

   private ISENode actualNode, root; 
   private AlgorithmicDebug debug; 
   private Call actualCall;
   private ListenerList listeners = new ListenerList();
   private IWorkbenchPage workbenchpage = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
   private IViewPart variablesSelectionView;
   private VariablesSelectionView view;
   Label lblMethodName;
   Combo combo ;
   private Text textParameters, textReturn, textConstraints;

   public AlgorithmicDebugView() throws PartInitException{
      variablesSelectionView = workbenchpage.showView("org.key_project.sed.ui.view.VariablesSelectionView",null,IWorkbenchPage.VIEW_ACTIVATE);
   }

   private void reset(){
      debug.unhighlight();
      debug.removeAllAlgoDebugAnnotations(root);
      debug = new AlgorithmicDebug();
      actualCall = null;
      lblMethodName.setText("");
      textConstraints.setText("");
      textReturn.setText("");
      IViewPart part = workbenchpage
            .findView("org.key_project.sed.ui.view.VariablesSelectionView");
      if (part instanceof VariablesSelectionView) {
         VariablesSelectionView view = (VariablesSelectionView) part;
         view.clear();
         view.getContent();        }

   }
   public void clear(){
      debug.unhighlight();
      debug.removeAllAlgoDebugAnnotations(root);
      lblMethodName.setText("");
      textConstraints.setText("");
      textReturn.setText("");
      actualNode = null;
      debug = null;
      actualCall = null;
      IViewPart part = workbenchpage
            .findView("org.key_project.sed.ui.view.VariablesSelectionView");
      if (part instanceof VariablesSelectionView) {
         VariablesSelectionView view = (VariablesSelectionView) part;
         view.clear();
      }

   }

   public void dispose(){
      if(debug != null){
         debug.unhighlight();
         debug.removeAllAlgoDebugAnnotations(root);
         debug = null;}
      IViewPart part = workbenchpage
            .findView("org.key_project.sed.ui.view.VariablesSelectionView");
      if (part instanceof VariablesSelectionView) {
         VariablesSelectionView view = (VariablesSelectionView) part;
         view.clear();
      }
      super.dispose();
   }

   private void showQuestionCall(Call call){
      try {
         //System.out.println("Showing Return: " + call.getRet().getName().toString());
         debug.unhighlight();
         debug.highlightCall(call);
         lblMethodName.setText(call.getCall().getName().toString());
         StringBuffer constraintText = new StringBuffer();
         for( ISEConstraint c : call.getRet().getConstraints()){
            constraintText.append("\n"+c.getName());
         }
         textConstraints.setText(constraintText.toString());
         textReturn.setText(call.getRet().getName().toString());
//         textReturn.setText(call.getRet().getCallStack());
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


   @Override
   public void createPartControl(final Composite parent) {
      Display display = Display.getDefault();

      parent.setLayout(new GridLayout(4, false));

      Button btnBack = new Button(parent, SWT.NONE);
      btnBack.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, false, false, 1, 1));
      btnBack.setText("Back");
      btnBack.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            if(debug != null){

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

            }}
      });

      final Button btnStart = new Button(parent, SWT.NONE);
      btnStart.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, false, false, 1, 1));
      btnStart.setText("Start");
      btnStart.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            if(btnStart.getText().equals("Start")){
               debug = new AlgorithmicDebug();
               actualNode = getSelectedNode();
               if(actualNode != null){
                  //System.out.println("STARTKNOTEN: " +getSelectedNode().toString());
                  btnStart.setText("Reset");
                  root = debug.getRoot(actualNode);
                  actualCall = debug.getCallTree(actualNode, combo.getText()).getStartCall();
                  IViewPart part = workbenchpage
                        .findView("org.key_project.sed.ui.view.VariablesSelectionView");
                  if (part instanceof VariablesSelectionView) {
                     VariablesSelectionView view = (VariablesSelectionView) part;
                     view.getContent();
                  }

                  if(actualCall != null){
                     showQuestionCall(actualCall);
                     setVariablesSelectionViewSelection();
                  }
               }
            }
            else if(btnStart.getText().equals("Reset")){
               reset();
               actualNode = getSelectedNode();                   //actualNode = debug.selectNode(getSelectedNode()); geändert: warum wurde der erste nicht markierte Node gesucht ??
               IViewPart part = workbenchpage
                     .findView("org.key_project.sed.ui.view.VariablesSelectionView");
               if (part instanceof VariablesSelectionView) {
                  VariablesSelectionView view = (VariablesSelectionView) part;
                  view.getContent();
               }

               if(actualNode != null){
                  //System.out.println("STARTKNOTEN: " +getSelectedNode().toString());
                  actualCall = debug.getCallTree(actualNode, combo.getText()).getStartCall();
                  if(actualCall != null){
                     showQuestionCall(actualCall);
                     setVariablesSelectionViewSelection();
                  }
               }
               else{
                  btnStart.setText("Start");
                  clear();
               }
            }
         }
      }
            );

      combo = new Combo(parent, SWT.NONE);
      combo.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false, 1, 1));
      String[] items = { "Bottom Up", "Top Down","Single Stepping" };
      combo.setItems(items);
      combo.select(0);

      Button btnNext = new Button(parent, SWT.NONE);
      btnNext.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, false, false, 1, 1));
      btnNext.setText("Next");
      btnNext.addSelectionListener(new SelectionAdapter() {

         @Override
         public void widgetSelected(SelectionEvent e) {
            if(debug != null){
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
            }}
      });

      Label lblNewLabel = new Label(parent, SWT.NONE);
      lblNewLabel.setLayoutData(new GridData(SWT.CENTER, SWT.CENTER, false, false, 4, 1));
      lblNewLabel.setText("Is the method doing the right thing ?");

      lblMethodName = new Label(parent, SWT.NONE);
      lblMethodName.setLayoutData(new GridData(SWT.CENTER, SWT.CENTER, false, false, 4, 1));

      Label lblWhileUsingThese = new Label(parent, SWT.NONE);
      lblWhileUsingThese.setLayoutData(new GridData(SWT.CENTER, SWT.CENTER, false, false, 4, 1));
      lblWhileUsingThese.setText("while using these constraints");

      textConstraints = new Text(parent, SWT.BORDER | SWT.READ_ONLY | SWT.V_SCROLL | SWT.H_SCROLL);
      GridData gd_textConstraints = new GridData(SWT.FILL, SWT.CENTER, true, false, 4, 1);
      gd_textConstraints.heightHint = 100;
      textConstraints.setLayoutData(gd_textConstraints);

      Listener scrollBarListener = new Listener () {
         @Override
         public void handleEvent(Event event) {
            Text t = (Text)event.widget;
            Rectangle r1 = t.getClientArea();
            Rectangle r2 = t.computeTrim(r1.x, r1.y, r1.width, r1.height);
            Point p = t.computeSize(SWT.DEFAULT,  SWT.DEFAULT,  true);
            t.getHorizontalBar().setVisible(r2.width <= p.x);
            t.getVerticalBar().setVisible(r2.height <= p.y);
            if (event.type == SWT.Modify) {
               t.getParent().layout(true);
               t.showSelection();
            }
         }
      };
      textConstraints.addListener(SWT.Resize, scrollBarListener);
      textConstraints.addListener(SWT.Modify, scrollBarListener);

      Label lblNewLabel_1 = new Label(parent, SWT.NONE);
      lblNewLabel_1.setLayoutData(new GridData(SWT.CENTER, SWT.CENTER, false, false, 4, 1));
      lblNewLabel_1.setText("these parameters");

      textParameters = new Text(parent, SWT.BORDER | SWT.READ_ONLY | SWT.V_SCROLL | SWT.H_SCROLL);
      GridData gd_textParameters = new GridData(SWT.FILL, SWT.CENTER, true, false, 4, 1);
      gd_textParameters.heightHint = 100;
      textParameters.setLayoutData(gd_textParameters);

      textParameters.addListener(SWT.Resize, scrollBarListener);
      textParameters.addListener(SWT.Modify, scrollBarListener);

      Label lblNewLabel_2 = new Label(parent, SWT.NONE);
      lblNewLabel_2.setLayoutData(new GridData(SWT.CENTER, SWT.CENTER, false, false, 4, 1));
      lblNewLabel_2.setText("and this return value");

      textReturn = new Text(parent, SWT.BORDER | SWT.READ_ONLY | SWT.V_SCROLL | SWT.H_SCROLL);
      GridData gd_textReturn = new GridData(SWT.FILL, SWT.CENTER, true, false, 4, 1);
      gd_textReturn.heightHint = 50;
      textReturn.setLayoutData(gd_textReturn);
      textReturn.addListener(SWT.Resize, scrollBarListener);
      textReturn.addListener(SWT.Modify, scrollBarListener);

      Button btnCorrect = new Button(parent, SWT.NONE);
      btnCorrect.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, false, false, 1, 1));
      btnCorrect.setText("Correct");
      Color green = display.getSystemColor(SWT.COLOR_GREEN);
      btnCorrect.setBackground(green);
      btnCorrect.addListener(SWT.Selection, new Listener() {
         public void handleEvent(Event e) {
            switch (e.type) {
            case SWT.Selection:
               //               MessageBox mbo = new MessageBox( parent.getShell());
               //               mbo.setText("Stack");
               //               try {
               //                  mbo.setMessage(actualCall.getCall().getCallStack().toString());
               //               }
               //               catch (DebugException e1) {
               //                  // TODO Auto-generated catch block
               //                  e1.printStackTrace();
               //               }
               //               mbo.open();

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

      Button btnFalse = new Button(parent, SWT.NONE);
      btnFalse.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, false, false, 1, 1));
      btnFalse.setText("False");
      Color red = display.getSystemColor(SWT.COLOR_RED);
      btnFalse.setBackground(red);
      btnFalse.addListener(SWT.Selection, new Listener() {
         public void handleEvent(Event e) {
            switch (e.type) {
            case SWT.Selection:
               if(actualCall != null){
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
            }}
      });

      new Label(parent, SWT.NONE);
      new Label(parent, SWT.NONE);

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
      lblMethodName.setFocus();
      if(actualCall != null)
         setVariablesSelectionViewSelection();
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
