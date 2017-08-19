package org.key_project.sed.algodebug.model2;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.algodebug.searchstrategy.ISearchStrategy;
import org.key_project.sed.algodebug.searchstrategy.BottomUp;
import org.key_project.sed.algodebug.searchstrategy.SingleStepping;
import org.key_project.sed.algodebug.searchstrategy.TopDown;
import org.key_project.sed.core.model.ISEBaseMethodReturn;
import org.key_project.sed.core.model.ISEExceptionalMethodReturn;
import org.key_project.sed.core.model.ISEExceptionalTermination;
import org.key_project.sed.core.model.ISEMethodCall;
import org.key_project.sed.core.model.ISEMethodReturn;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEThread;

public class ListOfMethodCallTrees {

   /*
    * the list of paths
    * @author Peter Schauberger
    */
   public ArrayList<MethodCall> listOfMethodCallTrees;

   /*
    * @return the paths
    * @author Peter Schauberger
    */
   public ArrayList<MethodCall> getListOfMethodCallTrees() {
      return listOfMethodCallTrees;
   }

   /*
    * Constructor
    * @author Peter Schauberger
    */
   public ListOfMethodCallTrees() {
      this.listOfMethodCallTrees = new ArrayList<MethodCall>();

   }
   
   private ISearchStrategy searchStrategy = null; 

   /*
    * Iterator for lists of paths
    * @author Peter Schauberger
    */
   private int methodCallTreeIterator;

   /*
    * iterator for the list of calls of a specific path
    */
   private int methodCallIterator;

   public void setTraversalStrategy(ISearchStrategy strategy){
      this.searchStrategy = strategy;
   }

   public void addParentsToTree(){
      for(MethodCall call:listOfMethodCallTrees){
         call.setParent(null);
         addParentsToSubTree(call);
      }
   }
   
   private void addParentsToSubTree(MethodCall call){
      for(MethodCall subCall:call.getListOfCalledMethods()){
         subCall.setParent(call);
         addParentsToSubTree(subCall);
      }
   }
   
   public void generateListOfCallTrees(ISENode node){
      try {
         //System.out.println("Generating Paths");
         if(!node.hasChildren()) { //Bei einem Blatt angekommen
            List<ISENode> list =  getListOfPathNodes(node);
//            System.out.println("PrintList");
//            for(ISENode printme :list){
//               try {
//                  System.out.println(printme.getName().toString());
//               }
//               catch (DebugException e) {
//                  // TODO Auto-generated catch block
//                  e.printStackTrace();
//               }
//            }
            MethodCall tree = generateSubTree(list.get(0), list);
            tree.setMethodCallTreeCompletelySearched(false);
            tree.setRoot();
            listOfMethodCallTrees.add(tree);
         }
         else{
            for(ISENode child : node.getChildren()){ //Es gibt Kind-Knoten: Für jeden neuen Pfad hinzufügen
               generateListOfCallTrees(child);
            }
         }
      }
      catch (DebugException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }

   }

   private MethodCall generateSubTree(ISENode start, List<ISENode> nodelist){
      ArrayList<MethodCall> calllist = new ArrayList<MethodCall>();
      int nodecount = 0;
      int counter = 0;
      ISENode stop = null;
      if(!nodelist.isEmpty()){
         List<ISENode> nodelistIntern = nodelist.subList(1, nodelist.size()-1);
         for(ISENode node : nodelistIntern){
            nodecount++;
            if((node instanceof ISEMethodCall) && counter == 0){
               counter++;
               calllist.add(generateSubTree(node, (List<ISENode>)nodelist.subList(nodecount, nodelist.size()-1)));
//               try {
//                  System.out.println("Füge Subtree hinzu: Oberknoten" +start.getName().toString() +" Unternkoten "+node.getName().toString());
//               }
//               catch (DebugException e) {
//                  // TODO Auto-generated catch block
//                  e.printStackTrace();
//               }
            }
            else if((node instanceof ISEMethodReturn) && counter == 0) {
               counter--;
               return new MethodCall(start, node, calllist);
            }
            else if((node instanceof ISEMethodReturn) && counter != 0) 
               counter--;
            else if((node instanceof ISEMethodCall) && counter != 0) 
               counter++;
            else if((node instanceof ISEExceptionalMethodReturn)){ 
//               System.out.println("Exceptional Method Return");
               stop = node;
               break;
            }

         }
      }
      //      try {
      //         System.out.println("Füge Call hinzu: " +start.getName().toString() +" Unternkoten "+stop.getName().toString());
      //      }
      //      catch (DebugException e) {
      //         // TODO Auto-generated catch block
      //         e.printStackTrace();
      //      }
      if(stop == null)
         System.out.println("");
      return new MethodCall(start, stop, calllist);
   }

   private List<ISENode> getListOfPathNodes(ISENode leaf){
      ISENode node = leaf;
      List<ISENode> list = new ArrayList<ISENode>();
      //            System.out.println("Generiere Pfad-Liste:");
      while(!(node instanceof ISEThread)){
         list.add(0, node);
         try {
            node = node.getParent();
         }
         catch (DebugException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
         }
      }
      //      Collections.reverse(list);

      return list;
   }

   public void printTree(){
      for(MethodCall path : listOfMethodCallTrees){
         printListOfCallTrees(path);
      }
   }

   private void  printListOfCallTrees(MethodCall oberknoten){
      if(!oberknoten.getListOfCalledMethods().isEmpty()){

      try {
         System.out.println("OberKnoten von: "+(oberknoten.getCall()).getName().toString() + " nach: " + (oberknoten.getMethodReturn()).getName().toString());
      }
      catch (DebugException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }}
      for(MethodCall unterknoten : oberknoten.getListOfCalledMethods()){
         try {
            System.out.println("Unterknoten von: "+(unterknoten.getCall()).getName().toString()+" nach: "+(unterknoten.getMethodReturn()).getName().toString());
            //            printListOfCallTrees(unterknoten);
         }
         catch (DebugException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
         }
 
      }
      if(!oberknoten.getListOfCalledMethods().isEmpty()){
         for(MethodCall unterknoten2 : oberknoten.getListOfCalledMethods()){

            printListOfCallTrees(unterknoten2);}
      }
   }

}
