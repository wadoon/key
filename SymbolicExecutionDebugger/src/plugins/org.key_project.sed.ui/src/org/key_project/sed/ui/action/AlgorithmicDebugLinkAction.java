package org.key_project.sed.ui.action;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.MessageBox;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.ui.action.AlgorithmicDebugCorrectAnnotationLinkAction;

/**
 * @author Peter Schauberger
 */
public class AlgorithmicDebugLinkAction implements ISEAnnotationLinkAction {

   /**
    * If there is a node doing wrong things it is returned via this Node.
    */
   private ISENode buggyNode;
   
   /**
    * Call the algorithmic debugging method.
    * @param shell   The current {@link Shell}.
    * @param node    The selected {@link ISENode}.
    */
   @Override
   public void run(Shell shell, ISENode node) {
    
      int result = generalAlgoritm(shell, node);
      
      switch(result){
      case 0:
         MessageBox m1 = new MessageBox(
               shell, 
               SWT.OK);
             m1.setText("Cancel");
             m1.setMessage("Algorithmic Debugging canceled");
             m1.open();
             break;
      case 1:
         MessageBox m2 = new MessageBox(
               shell, 
               SWT.OK);
             m2.setText("Success, no errors found.");
             m2.setMessage("You answered all the nodes to be correct, so the program should run fine.");
             m2.open();
             break;
      case 2:
         MessageBox m3 = new MessageBox(
               shell, 
               SWT.OK);
             m3.setText("Success, found an error.");
             m3.setMessage("The Node " + buggyNode.toString() + "is the incorrect part of the Code.");
             m3.open();
             break;
             }
      }
   
   /**
    * General algorithm for algorithmic debugging. 
    * @param shell   The current {@link Shell}.
    * @param node    The selected {@link ISENode}.
    * @return        int value that varies by the answers of the user. If the user cancels the debugging, 0 is returned. If no bug was found 1 is returned. If a bug was found, 2 is returned.
    */
   public int generalAlgoritm(Shell shell, ISENode worknode){
      
      //Frage so lange Knoten ab, bis keine mehr übrig sind oder ein falscher Knoten gefunden wurde.
      int answer = 0;
      ISENode node;
      do{
         node = selectNode(worknode);
         if(node == null)
            return 1;
         answer = askNode(node);
      
//         if (answer == null) return null;
//         answer.markNodes();
         
         switch(answer){
         case 0:
            return 0;
         case 1:
            annotateNode(shell, node, true);
            continue;
         case 2:
            annotateNode(shell, node, false);
            buggyNode = node;
            return 2;
            }
         }while(answer == 1);
      return 1;
   }
   
   /**
    * Method for calling the annotation methods.
    * @param shell   The current {@link Shell}.
    * @param node    The selected {@link ISENode}.
    * @param value   The state the Node should be annotated with. True for a "correct" annotation, false for a "false" annotation.
    */
   private void annotateNode(Shell shell, ISENode node, boolean value){
      
      AlgorithmicDebugCorrectAnnotationLinkAction ac = new AlgorithmicDebugCorrectAnnotationLinkAction();
      AlgorithmicDebugFalseAnnotationLinkAction af = new AlgorithmicDebugFalseAnnotationLinkAction();
      if(value)
         ac.run(shell, node);
      else
         af.run(shell, node);
      }
   
   /**
    * Method to find the next node of the Symbolic Execution Tree that should be asked.
    * @param node    The selected {@link ISENode}.
    * @return        Next node to ask {@link ISENode} or null if all nodes have been visited.
    */
   //selectNode wählt den nächsten Knoten der noch nicht annotiert wurde.
   private ISENode selectNode(ISENode node){
      AlgorithmicTraversal at = new AlgorithmicTraversal();
      at.setStrategie(new TraversalStrategyPreOrder());
      
      return at.traverse(node);
   }
   
   /**
    * Method to ask the user if the given node is correct or false.
    * @param node    The selected {@link ISENode}.
    * @return        int value stating the choice of the user. 0 means the user wants to stop algorithmic debugging, 1 means the node is correct, 2 means the node is false.
    */
   private int askNode(ISENode node){
      Shell shell = Display.getCurrent().getActiveShell();
      
      MessageBox mb = new MessageBox(shell, SWT.ICON_INFORMATION | SWT.YES | SWT.NO | SWT.CANCEL);
      mb.setText("Question");
      mb.setMessage("Is this Node doing the right thing? \n"+node.toString());
      mb.open();
          
      int val = mb.open();

      switch (val) {
         case SWT.CANCEL:
            return 0;
         case SWT.YES:
            return 1;
         case SWT.NO:
            return 2; 
          }
      return 0;
   }
  
}