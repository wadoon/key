package org.key_project.sed.algodebug.model;

import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedList;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEBaseMethodReturn;
import org.key_project.sed.core.model.ISEExceptionalMethodReturn;
import org.key_project.sed.core.model.ISEMethodCall;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEThread;

public class CallTree {
   
   /*
    * the list of paths
    * @author Peter Schauberger
    */
   public ArrayList<CallPath> Paths;
   
   /*
    * @return the paths
    * @author Peter Schauberger
    */
   public ArrayList<CallPath> getPaths() {
      return Paths;
   }

   /*
    * Constructor
    * @author Peter Schauberger
    */
   public CallTree() {
      this.Paths = new ArrayList<CallPath>();
      
   }

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
      if(pathIterator == Paths.size()-1){ //letzter Pfad erreicht
         if(callIterator == Paths.get(pathIterator).getSize()-1){ //Letzter Call im letzten Pfad: Ende erreicht
            return null; 
         }
         else{ //mitten im letzten Pfad: nächsten Call zurück
            callIterator++;
            return Paths.get(pathIterator).getCall(callIterator);
            }
      }
      else{ // nicht letzter Pfad
         if(callIterator == Paths.get(pathIterator).getSize()-1){ //Letzter Call im Pfad: erster Call im nächsten Pfad zurück
            pathIterator++;
            callIterator = 0;
            return Paths.get(pathIterator).getCall(callIterator); 
         }
         else{
            callIterator++;
            return Paths.get(pathIterator).getCall(callIterator); 
         }
         
      }
   }

   public Call getStartCall(){
      pathIterator = 0;
      callIterator = 0;
      return Paths.get(pathIterator).getCall(callIterator);
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
            return Paths.get(pathIterator).getCall(callIterator);
         }
      }
      else{
         if(callIterator == 0){ //erster Call in irgendeinem Pfad: einen Pfad zuvor letzten Call zurück
            pathIterator--;
            callIterator = Paths.get(pathIterator).getSize()-1;
            return Paths.get(pathIterator).getCall(callIterator);
         }
         else{ //irgendwo in einem Pfad: gib vorigen Call zurück
            callIterator--;
            return Paths.get(pathIterator).getCall(callIterator);
         }
      }
      
   }
   
   /*
    * returns the root node of the symbolic tree
    * @author Peter Schauberger
    */
   private ISENode getRoot(ISENode node){
      System.out.println("getRoot");
      try {
         if(node.getParent() == null) //Dann haben wir bereits den Root-Knoten gefunden
            return node;
         else if( node.getParent() instanceof ISEThread)
            return node.getParent();
         else
            return getRoot(node.getParent());
      }
      catch (DebugException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }

      return node;
   }
   
   /*
    * Generate the Paths for algorithmic debugging
    * @author Peter Schauberger
    */
   public ArrayList<CallPath> generatePaths(ISENode node){
         try {
            //System.out.println("Generating Paths");
            if(!node.hasChildren()) { //Bei einem Blatt angekommen
               addPath(node);
               }
            else{
               for(ISENode child : node.getChildren()){ //Es gibt Kind-Knoten: Für jeden neuen Pfad hinzufügen
                  generatePaths(child);
                  }
               }
            return Paths;
            }
       catch (DebugException e) {
          // TODO Auto-generated catch block
          e.printStackTrace();
       }
   return null;
   }
   
   /*
    * Erzeugt einen Path indem es von einem Blatt zur Wurzel läuft
    * @author Peter Schauberger
    */
   private void addPath(ISENode leaf){
      try {
      ISENode node = leaf;
      CallPath path = new CallPath();
      Deque<ISENode> deque = new LinkedList<ISENode>();
      
         while(!(node instanceof ISEThread)){
            if(node instanceof ISEBaseMethodReturn){
               deque.push(node);
               //System.out.println("Pushing"+node.getName());
            }
            else if(node instanceof ISEMethodCall){
               //System.out.println("Adding Call: From "+node.getName());//+"to"+deque.getFirst().getName());
               if(!( deque.peekLast() instanceof ISEExceptionalMethodReturn))
                  path.addCall(new Call(node, deque.pop()));
               else
                  path.addCall(new Call(node, deque.peekLast()));
            }
               node = node.getParent();
            }
      
         Paths.add(path);
         
         }
         catch (DebugException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
         }
   }

   /*
    * Print the generated Paths to the Console
    * @author Peter Schauberger
    */
   public void printPathsToConsole(){
      System.out.println("Printing Paths to Console:");
      int counter = 0;
      for(CallPath path : Paths){
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
