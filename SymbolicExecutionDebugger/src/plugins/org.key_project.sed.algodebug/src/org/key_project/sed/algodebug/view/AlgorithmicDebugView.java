package org.key_project.sed.algodebug.view;

import java.util.ArrayList;
import java.util.List;
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
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.key_project.sed.algodebug.model.AlgorithmicDebugger;
import org.key_project.sed.algodebug.model.Execution;
import org.key_project.sed.algodebug.searchstrategy.SingleStepping;
import org.key_project.sed.algodebug.searchstrategy.TopDown;
import org.key_project.sed.algodebug.util.ExecutionTreeUtil;
import org.key_project.sed.algodebug.util.SETUtil;
import org.key_project.sed.core.model.ISEConstraint;
import org.key_project.sed.core.model.ISEExceptionalMethodReturn;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.key.core.model.KeYMethodCall;
import org.key_project.sed.key.core.model.KeYMethodReturn;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.sed.ui.visualization.execution_tree.feature.ExceptionalMethodReturnCreateFeature;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Text;

@SuppressWarnings("unused")
public class AlgorithmicDebugView extends ViewPart implements Observer, ISelectionProvider{

   public static final String VIEW_ID = "org.key_project.sed.ui.view.AlgorithmicDebugView";
   private ISENode actualNode, root; 
   private AlgorithmicDebugger debug; 
   private Execution actualCall;
   private ListenerList listeners = new ListenerList();
   private IWorkbenchPage workbenchpage = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
   private IViewPart variablesSelectionView;
   private VariablesSelectionView view;
   private Label lblMethodName;
   private Combo combo ;
   private Text textParameters, textReturn, textConstraints;
   private ArrayList<Execution> questionList;
   private Button btnStart, btnCorrect, btnFalse;
   private List<Execution> chronik = new ArrayList<Execution>();
   private Shell shell = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell();
   private int chronikCounter = 0;

   /*
    * constructor
    */
   public AlgorithmicDebugView() throws PartInitException{
      variablesSelectionView = workbenchpage.showView("org.key_project.sed.ui.view.VariablesSelectionView",null,IWorkbenchPage.VIEW_ACTIVATE);
   }

   /*
    * List of text strings used for the combo field used to select the search strategy by the user
    */
   String[] items = { "Single Stepping","Top Down" };

   /*
    * setsearchstrategy
    * Create new Strategy Object for searching based on user decision at combo
    * See Strategy Patten
    */
   private void setsearchstrategy(){
      switch (combo.getText()){
      case "Single Stepping": debug.setSearchStrategy(new SingleStepping()); break;
      case "Top Down": debug.setSearchStrategy(new TopDown()); break;
      }
   }

   /*
    * set the actual exection to be correct and get the next execution selected by the search strategy
    * if the next execution to be asked is null, ask the algorithmicdebug object why null is returned 
    */
   private void correctButtonPressed(){
      debug.unhighlight();
      debug.markCall(actualCall, 'c');
      Execution next =  debug.getNext();
      if(next != null){
         chronik.add(next);
         chronikCounter = chronik.size()-1;
         actualCall = next;
         debug.highlightCall(actualCall);
         showQuestion(actualCall);
         setVariablesSelectionViewSelection(actualCall);
      }
      else{
         askDebugWhyThereIsNoNextExecutionToAsk();
      }
   }

   /*
    * set the actual exection to be false and get the next execution selected by the search strategy
    * if the next execution to be asked is null, ask the algorithmicdebug object why null is returned 
    */
   private void falseButtonPressed(){
      debug.unhighlight();
      debug.markCall(actualCall, 'f');

      Execution next =  debug.getNext();
      if(next != null){
         chronik.add(next);
         chronikCounter = chronik.size()-1;
         actualCall = next;
         debug.highlightCall(actualCall);
         showQuestion(actualCall);
         setVariablesSelectionViewSelection(actualCall);
      }
      else{
         askDebugWhyThereIsNoNextExecutionToAsk();
      }
   }

   /*
    * if every exeution tree was searched completey and no bug was found, let the user know about
    * if a bug was found let the user know about
    */
   private void askDebugWhyThereIsNoNextExecutionToAsk(){
      if(debug.bugFound()){
         Execution bug = debug.getBug();
         btnCorrect.setEnabled(false);
         btnFalse.setEnabled(false);
         ExecutionTreeUtil.annotateSETNodesOfABuggyExecution(bug);
         notifyBugFound(bug);
      }
      else if(debug.searchCompletedButNoBugFound()){
         btnCorrect.setEnabled(false);
         btnFalse.setEnabled(false);
         notifyNoBugFound();
      }
   }

   /*
    * no bug was found, let the user know about 
    */
   private void notifyNoBugFound() {
      MessageBox mb = new MessageBox(shell);
      mb.setText("Couldn't find a Bug in the method");
      mb.setMessage("It seems method not contains a bug.");
      mb.open();
   }

   /*
    * starts the algorithmic debug process by creating all needed sources and getting the first execution that has to be asked
    */
   private void startButtonPressed() {
      btnCorrect.setEnabled(true);
      btnFalse.setEnabled(true);
      debug = new AlgorithmicDebugger();
      setsearchstrategy();
      actualNode = getSelectedNode();
      if(actualNode != null){
         btnStart.setText("Reset");
         root = SETUtil.getRoot(actualNode);
         debug.generateTree(root);
         SETUtil.init(root);
         actualCall = debug.getNext();
         IViewPart part = workbenchpage
               .findView("org.key_project.sed.ui.view.VariablesSelectionView");
         if (part instanceof VariablesSelectionView) {
            VariablesSelectionView view = (VariablesSelectionView) part;
            view.getContent();
         }
         if(actualCall != null){
            chronik.add(actualCall);
            chronikCounter = chronik.size()-1;
            debug.highlightCall(actualCall);
            showQuestion(actualCall);
            setVariablesSelectionViewSelection(actualCall);
         }
      }
      else{
         MessageBox mb = new MessageBox(shell);
         mb.setText("No node selected !");
         mb.setMessage("Please select a node in the Symbolic Execution Tree View bevor you start Algorithmic Debugging.");
         mb.open();
      }
   }

   /*
    * show and highlight the next execution of the asked execution history
    */
   protected void nextButtonPressed() {
      if(debug != null && chronikCounter < chronik.size()-1){
         chronikCounter++;
         Execution call = chronik.get(chronikCounter);
         showQuestion(call);
         setVariablesSelectionViewSelection(call);
      }
      else{
         MessageBox mb = new MessageBox(shell);
         mb.setText("Last Call reached");
         mb.setMessage("There is no call after this one.");
         mb.open();
      }
   }

   /*
    * show and highlight the previous execution of the asked execution history
    */
   protected void backButtonPressed() {
      if(debug != null && chronikCounter >= 1){
         chronikCounter--;
         Execution call = chronik.get(chronikCounter);
         showQuestion(call);
         setVariablesSelectionViewSelection(call);
      }
      else{
         MessageBox mb = new MessageBox(shell);
         mb.setText("First call reached!");
         mb.setMessage("There is no call before this one.");
         mb.open();
      }
   }

   /*
    * clears the ressouorces needed for the algorithmic debugging process and sets them new
    */
   private void reset(){
      clear();
      if(actualNode != null){
         btnCorrect.setEnabled(true);
         btnFalse.setEnabled(true);
         startButtonPressed();
      }
      else{
         btnStart.setText("Start");
      }
   }

   /*
    * Unhighlight last call, remove all annotations, set all textfields to "",delete debug and actual call elements and reset other views.
    */
   private void clear(){
      debug.unhighlight();
      SETUtil.removeAllAlgoDebugAnnotations(root);
      lblMethodName.setText("");
      textConstraints.setText("");
      textReturn.setText("");
      textParameters.setText("");
      actualNode = null;
      debug = null;
      actualCall = null;
      chronikCounter = 0;
      IViewPart part = workbenchpage
            .findView("org.key_project.sed.ui.view.VariablesSelectionView");
      if (part instanceof VariablesSelectionView) {
         VariablesSelectionView view = (VariablesSelectionView) part;
         view.clear();
      }
   }

   /*
    * (non-Javadoc)
    * @see org.eclipse.ui.part.WorkbenchPart#dispose()
    */
   public void dispose(){
      //      clear();
      super.dispose();
   }

   /*
    * Unhighlight last call, highlight actual call and fill all necessary UI textfields
    */
   public void showQuestion(Execution call){
      try {
         debug.unhighlight();
         debug.highlightCall(call);
         lblMethodName.setText(call.getCall().getName().toString());
         StringBuffer constraintText = new StringBuffer();
         for( ISEConstraint c : call.getExecutionReturn().getConstraints()){
            constraintText.append("\n"+c.getName());
         }
         textConstraints.setText(constraintText.toString());
         textReturn.setText(call.getExecutionReturn().getName().toString());
         //         textReturn.setText(call.getRet().getCallStack());
         /*
         if(!(call.getExecutionReturn() instanceof ISEExceptionalMethodReturn)){
            KeYMethodReturn ret = (KeYMethodReturn) call.getExecutionReturn();
            try {
               ret.getExecutionNode().getReturnValues();
               textReturn.setText(ret.toString());
            }
            catch (Exception e2) {
               e2.printStackTrace();
            }
         }
         else {
            textReturn.setText("");
         }
          */
         KeYMethodCall methodcall = (KeYMethodCall) call.getCall();
         methodcall.getExecutionNode().getMethodReference().getArguments();
         textParameters.setText(methodcall.getExecutionNode().getMethodReference().getArguments().toString());
      }
      catch (DebugException e) {
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

   /*
    * (non-Javadoc)
    * @see org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets.Composite)
    */
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
            backButtonPressed();}
      });

      btnStart = new Button(parent, SWT.NONE);
      btnStart.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, false, false, 1, 1));
      btnStart.setText("Start");
      btnStart.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            if(btnStart.getText().equals("Start")){
               startButtonPressed();
            }
            else if(btnStart.getText().equals("Reset")){
               reset();
            }
         }
      }
            );

      combo = new Combo(parent, SWT.NONE);
      combo.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true, false, 1, 1));
      combo.setItems(items);
      combo.select(0);

      Button btnNext = new Button(parent, SWT.NONE);
      btnNext.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, false, false, 1, 1));
      btnNext.setText("Next");
      btnNext.addSelectionListener(new SelectionAdapter() {

         @Override
         public void widgetSelected(SelectionEvent e) {
            nextButtonPressed();}
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

      btnCorrect = new Button(parent, SWT.NONE);
      btnCorrect.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, false, false, 1, 1));
      btnCorrect.setText("Correct");
      Color green = display.getSystemColor(SWT.COLOR_GREEN);
      btnCorrect.setBackground(green);
      btnCorrect.addListener(SWT.Selection, new Listener() {
         public void handleEvent(Event e) {
            switch (e.type) {
            case SWT.Selection:{
               correctButtonPressed();
               break;}
            }
         }

      });

      btnFalse = new Button(parent, SWT.NONE);
      btnFalse.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, false, false, 1, 1));
      btnFalse.setText("False");
      Color red = display.getSystemColor(SWT.COLOR_RED);
      btnFalse.setBackground(red);
      btnFalse.addListener(SWT.Selection, new Listener() {
         public void handleEvent(Event e) {
            switch (e.type) {
            case SWT.Selection:
               falseButtonPressed();
               break;
            }}
      });

      new Label(parent, SWT.NONE);
      new Label(parent, SWT.NONE);
   }

   /*
    * return all nodes of the symbolic execution tree as an array of ISENodes
    * Alle Knoten des Execution Tree in Preorder Reihenfolge in einem Array zurückgeben...
    */
   public Object[] getExecutionTreeAsArray(){
      ISENode root = null;
      if(actualNode != null){
         root = SETUtil.getRoot(actualNode);
      }
      Object[] array = null;
      if(root != null)
         array =  asList(root).toArray();
      return array;
   }

   /*
    * set the input of the variables selection view to the given execution
    * @param execution the exeution the stack should be shown of
    */
   private void setVariablesSelectionViewSelection(Execution execution) {
      SWTUtil.select(VariablesSelectionView.getviewerLeft(),
            new StructuredSelection(execution.getCall()), true);
      SWTUtil.select(VariablesSelectionView.getviewerRight(),
            new StructuredSelection(execution.getExecutionReturn()), true);
   }

   /*
    * returns a list containing all the ISENodes of the actual execution tree
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
         e.printStackTrace();
      }
      return list;
   }

   /*
    * (non-Javadoc)
    * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
    */
   @Override
   public void setFocus() {
      lblMethodName.setFocus();
      if(actualCall != null){
         setVariablesSelectionViewSelection(actualCall);
      }
   }

   /*
    * (non-Javadoc)
    * @see java.util.Observer#update(java.util.Observable, java.lang.Object)
    */
   @Override
   public void update(Observable o, Object arg) {
   }

   /*
    * (non-Javadoc)
    * @see org.eclipse.jface.viewers.ISelectionProvider#addSelectionChangedListener(org.eclipse.jface.viewers.ISelectionChangedListener)
    */
   @Override
   public void addSelectionChangedListener(ISelectionChangedListener listener) {
      listeners.add(listener);        
   }

   /*
    * (non-Javadoc)
    * @see org.eclipse.jface.viewers.ISelectionProvider#getSelection()
    */
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

   /*
    * (non-Javadoc)
    * @see org.eclipse.jface.viewers.ISelectionProvider#removeSelectionChangedListener(org.eclipse.jface.viewers.ISelectionChangedListener)
    */
   @Override
   public void removeSelectionChangedListener(ISelectionChangedListener listener) {
      listeners.remove(listener);        
   }

   /*
    * (non-Javadoc)
    * @see org.eclipse.jface.viewers.ISelectionProvider#setSelection(org.eclipse.jface.viewers.ISelection)
    */
   @Override
   public void setSelection(ISelection selection) {
      Object[] list = listeners.getListeners();
      for (int i = 0; i < list.length; i++) {
         ((ISelectionChangedListener) list[i])
         .selectionChanged(new SelectionChangedEvent(this, selection));
      }
   }

   /*
    * notify the user that a buggy execution was found
    * @param execution the buggy execution
    */
   public void notifyBugFound(Execution execution) {
      MessageBox mb = new MessageBox(shell);
      mb.setText("Incorrect Method identified");
      try {
         mb.setMessage("It seems Method " +execution.getCall().getName().toString()+" contains a bug.");
      }
      catch (DebugException e) {
         e.printStackTrace();
      }
      mb.open();
   }

}
