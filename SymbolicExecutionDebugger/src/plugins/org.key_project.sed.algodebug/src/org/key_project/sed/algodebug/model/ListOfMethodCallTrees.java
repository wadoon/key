package org.key_project.sed.algodebug.model;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.debug.core.DebugException;
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

   public void generateListOfMethodCallTrees(ISENode node){
      try {
         //System.out.println("Generating Paths");
         if(!node.hasChildren()) { //Bei einem Blatt angekommen
            List<ISENode> list =  getListOfPathNodes(node);
            //            printNodeList(list);
            //            System.out.println("PrintList");
            //            for(ISENode printme :list){
            //               try {
            //                  System.out.println(printme.getName().toString());
            //               }
            //               catch (DebugException e) {
            //                  e.printStackTrace();
            //               }
            //            }
            MethodCall tree = generateMethodCallTree(list.get(0), list);
            tree.setMethodCallTreeCompletelySearched(false);
            tree.setRoot();
            listOfMethodCallTrees.add(tree);
         }
         else{
            for(ISENode child : node.getChildren()){ //Es gibt Kind-Knoten: Für jeden neuen Pfad hinzufügen
               generateListOfMethodCallTrees(child);
            }
         }
      }
      catch (DebugException e) {
         e.printStackTrace();
      }
   }

   private MethodCall generateMethodCallTree(ISENode start, List<ISENode> nodelist){
      ArrayList<MethodCall> calllist = new ArrayList<MethodCall>();
      int nodecount = 0;
      int counter = 0;
      if(nodelist.size() > 1){
         for(ISENode node : nodelist){
            if(node == start) 
               continue;
            if((node instanceof ISEMethodCall) && counter == 0){
               counter++;
               int ende = nodelist.size();
               calllist.add(generateMethodCallTree(node, (List<ISENode>)nodelist.subList(nodecount, ende)));
            }
            else if(((node instanceof ISEMethodReturn) && counter == 0) ) {
               return new MethodCall(start, node, calllist);
            }
            else if((node instanceof ISEMethodReturn) && counter != 0) 
               counter--;
            else if((node instanceof ISEMethodCall) && counter != 0) 
               counter++;
            nodecount++;
         }
      }
      else{
         return new MethodCall(start, start, calllist);
      }
      int zahl = nodelist.size()-1;
      return new MethodCall(start, nodelist.get(zahl), calllist);
   }

   private void printNodeList(List<ISENode> nodelist){
      System.out.println("\n neue Knotenliste:");
      for(ISENode node : nodelist){
         try {
            System.out.println(node.getName().toString());
         }
         catch (DebugException e) {
            e.printStackTrace();
         }
      }
   }
   
   private List<ISENode> getListOfPathNodes(ISENode leaf){
      ISENode node = leaf;
      List<ISENode> list = new ArrayList<ISENode>();
      while(!(node instanceof ISEThread)){
         list.add(0, node);
         try {
            node = node.getParent();
         }
         catch (DebugException e) {
            e.printStackTrace();
         }
      }
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
            e.printStackTrace();
         }}
      for(MethodCall unterknoten : oberknoten.getListOfCalledMethods()){
         try {
            System.out.println("Unterknoten von: "+(unterknoten.getCall()).getName().toString()+" nach: "+(unterknoten.getMethodReturn()).getName().toString());
            //            printListOfCallTrees(unterknoten);
         }
         catch (DebugException e) {
            e.printStackTrace();
         }

      }
      if(!oberknoten.getListOfCalledMethods().isEmpty()){
         for(MethodCall unterknoten2 : oberknoten.getListOfCalledMethods()){

            printListOfCallTrees(unterknoten2);}
      }
   }

}
