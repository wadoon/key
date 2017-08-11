package org.key_project.sed.algodebug.model;

import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedList;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.algodebug.searchstrategy.ISearchStrategy;
import org.key_project.sed.algodebug.searchstrategy.BottomUp;
import org.key_project.sed.algodebug.searchstrategy.SingleStepping;
import org.key_project.sed.algodebug.searchstrategy.TopDown;
import org.key_project.sed.core.model.ISEBaseMethodReturn;
import org.key_project.sed.core.model.ISEExceptionalMethodReturn;
import org.key_project.sed.core.model.ISEExceptionalTermination;
import org.key_project.sed.core.model.ISEMethodCall;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEThread;

public class CallTree {

   /*
    * the list of paths
    * @author Peter Schauberger
    */
   public ArrayList<CallPath> tree;

   /*
    * @return the paths
    * @author Peter Schauberger
    */
   public ArrayList<CallPath> getPaths() {
      return tree;
   }

   /*
    * Constructor
    * @author Peter Schauberger
    */
   public CallTree() {
      this.tree = new ArrayList<CallPath>();

   }

   private ISearchStrategy strategy = null; 

   /*
    * Iterator for lists of paths
    * @author Peter Schauberger
    */
   private int pathIterator;

   /*
    * iterator for the list of calls of a specific path
    */
   private int callIterator;

   /*
    * @returns The next call of the list of paths if we iterate it path by path and inside the paths call by call
    * @author Peter Schauberger
    */
   public Call getNextCall(){
      if(pathIterator == tree.size()-1){ //letzter Pfad erreicht
         if(callIterator == tree.get(pathIterator).getSize()-1){ //Letzter Call im letzten Pfad: Ende erreicht
            return null; 
         }
         else{ //mitten im letzten Pfad: nächsten Call zurück
            callIterator++;
            return tree.get(pathIterator).getCall(callIterator);
         }
      }
      else{ // nicht letzter Pfad
         if(callIterator == tree.get(pathIterator).getSize()-1){ //Letzter Call im Pfad: erster Call im nächsten Pfad zurück
            pathIterator++;
            callIterator = 0;
            return tree.get(pathIterator).getCall(callIterator); 
         }
         else{
            callIterator++;
            return tree.get(pathIterator).getCall(callIterator); 
         }

      }
   }

   /*
    * Gibt den ersten Call der Pfadliste zurück.
    * @author Peter Schauberger
    */
   public Call getStartCall(){
      pathIterator = 0;
      callIterator = 0;
      return tree.get(pathIterator).getCall(callIterator);
   }


   /*
    * Gibt den vorigen Call der Pfadliste zurück wenn diese Call für Call rückwärts durchlaufen wird
    * @author Peter Schauberger
    */
   public Call getPreviousCall(){

      if(pathIterator == 0){
         if(callIterator == 0){ //erster Call im ersten Pfad: gibt keinen davor
            return null;
         }
         else{ //irgendein Call im ersten Pfad: voreriger zurück
            callIterator--;
            return tree.get(pathIterator).getCall(callIterator);
         }
      }
      else{
         if(callIterator == 0){ //erster Call in irgendeinem Pfad: einen Pfad zuvor letzten Call zurück
            pathIterator--;
            callIterator = tree.get(pathIterator).getSize()-1;
            return tree.get(pathIterator).getCall(callIterator);
         }
         else{ //irgendwo in einem Pfad: gib vorigen Call zurück
            callIterator--;
            return tree.get(pathIterator).getCall(callIterator);
         }
      }

   }

   public void setTraversalStrategy(ISearchStrategy strategy){
      this.strategy = strategy;
   }

   public void generateCallTree(ISENode root, String strategy){
      if(strategy.equalsIgnoreCase("BottomUp"))
         this.strategy = new BottomUp();
      else if(strategy.equalsIgnoreCase("TopDown"))
         this.strategy = new TopDown();
      else if(strategy.equalsIgnoreCase("SingleStepping"))
         this.strategy = new SingleStepping();
      tree = this.strategy.generateCallTree(root);
   }

   /*
    * Print the generated Paths to the Console
    * @author Peter Schauberger
    */
   public void printPathsToConsole(){
      System.out.println("Printing Paths to Console:");
      int counter = 0;
      for(CallPath path : tree){
         counter++;
         System.out.println("Path "+counter);
         for(int i = 0; i < path.getSize(); i++){
            try {
               System.out.println("Call: From "+path.getCall(i).getCall().getName()+" to "+path.getCall(i).getRet().getName());
            }
            catch (DebugException e) {
               // TODO Auto-generated catch block
               e.printStackTrace();
            }
         }
      }
   }   

}
