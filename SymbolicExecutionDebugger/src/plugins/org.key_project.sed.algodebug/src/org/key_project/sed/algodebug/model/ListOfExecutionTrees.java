package org.key_project.sed.algodebug.model;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEMethodCall;
import org.key_project.sed.core.model.ISEMethodReturn;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEThread;

public class ListOfExecutionTrees {

   /*
    * the list of paths
    * @author Peter Schauberger
    */
   public ArrayList<Execution> listOfExecutionTrees;

   /*
    * @return the paths
    * @author Peter Schauberger
    */
   public ArrayList<Execution> getListOfExecutionTrees() {
      return listOfExecutionTrees;
   }

   /*
    * Constructor
    * @author Peter Schauberger
    */
   public ListOfExecutionTrees() {
      this.listOfExecutionTrees = new ArrayList<Execution>();
   }

   /*
    * adds the parent to every execution of the execution tree
    */
   public void addParentsToTree(){
      for(Execution call:listOfExecutionTrees){
         call.setParent(null);
         addParentsToSubTree(call);
      }
   }

   /*
    * adds the parent to every execution of the sub execution tree
    */
   private void addParentsToSubTree(Execution call){
      for(Execution subCall:call.getListOfCalledMethods()){
         subCall.setParent(call);
         addParentsToSubTree(subCall);
      }
   }

   /*
    * generates the list of execution trees 
    * @param the root node of a symbolic exeution tree
    */
   public void generateListOfExecutionTrees(ISENode node){
      try {
         //System.out.println("Generating Paths");
         if(!node.hasChildren()) { //Bei einem Blatt angekommen
            List<ISENode> list =  getListOfPathNodes(node);
            Execution tree = generateExecutionTree(list.get(0), list);
            tree.setExecutionTreeCompletelySearched(false);
            tree.setRoot();
            listOfExecutionTrees.add(tree);
         }
         else{
            for(ISENode child : node.getChildren()){ //Es gibt Kind-Knoten: Für jeden neuen Pfad hinzufügen
               generateListOfExecutionTrees(child);
            }
         }
      }
      catch (DebugException e) {
         e.printStackTrace();
      }
   }

   /*
    * generates an exeution tree 
    * @param start the first node of the path ob which the execution tree is based
    * @param nodelist the list of nodes the path consists of
    */
   private Execution generateExecutionTree(ISENode start, List<ISENode> nodelist){
      ArrayList<Execution> calllist = new ArrayList<Execution>();
      int nodecount = 0;
      int counter = 0;
      if(nodelist.size() > 1){
         for(ISENode node : nodelist){
            if(node == start) 
               continue;
            if((node instanceof ISEMethodCall) && counter == 0){
               counter++;
               int ende = nodelist.size();
               calllist.add(generateExecutionTree(node, (List<ISENode>)nodelist.subList(nodecount+1, ende)));
            }
            else if(((node instanceof ISEMethodReturn) && counter == 0) ) {
               return new Execution(start, node, calllist);
            }
            else if((node instanceof ISEMethodReturn) && counter != 0) 
               counter--;
            else if((node instanceof ISEMethodCall) && counter != 0) 
               counter++;
            nodecount++;
         }
      }
      else{
         return new Execution(start, start, calllist);
      }
      int zahl = nodelist.size()-1;
      return new Execution(start, nodelist.get(zahl), calllist);
   }

   /*
    * prints the list of ISENodes to the console the given list consists of
    * @param nodelist a list of ISENodes
    */
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
      for(Execution path : listOfExecutionTrees){
         System.out.println("Knotenliste von Execution Tree");
         printListOfCallTrees(path);
      }
   }

   private void  printListOfCallTrees(Execution oberknoten){
      if(!oberknoten.getListOfCalledMethods().isEmpty()){

         try {
            System.out.println("OberKnoten von: "+(oberknoten.getCall()).getName().toString() + " nach: " + (oberknoten.getExecutionReturn()).getName().toString());
         }
         catch (DebugException e) {
            e.printStackTrace();
         }}
      for(Execution unterknoten : oberknoten.getListOfCalledMethods()){
         try {
            System.out.println("Unterknoten von: "+(unterknoten.getCall()).getName().toString()+" nach: "+(unterknoten.getExecutionReturn()).getName().toString());
            //            printListOfCallTrees(unterknoten);
         }
         catch (DebugException e) {
            e.printStackTrace();
         }

      }
      if(!oberknoten.getListOfCalledMethods().isEmpty()){
         for(Execution unterknoten2 : oberknoten.getListOfCalledMethods()){

            printListOfCallTrees(unterknoten2);}
      }
   }

   /*
    * prints the list of execution trees one after another to the console as sequence of strings
    * each tree can be plottet using graphviz
    */
   public void printTreeAsGraphviz() {
      for(Execution path : listOfExecutionTrees){
         System.out.println("digraph G {");
         try {
            System.out.println("<List of Execution Trees>"+" -> "+(path.getCall()).getName().toString());
         }
         catch (DebugException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
         }
         printListOfCallTreesAsGraphviz(path);
         System.out.println("}");
      }
   }

   private void  printListOfCallTreesAsGraphviz(Execution oberknoten){
      if(!oberknoten.getListOfCalledMethods().isEmpty()){
         for(Execution unterknoten : oberknoten.getListOfCalledMethods()){
            try {
               System.out.println((oberknoten.getCall()).getName().toString()+" -> "+(unterknoten.getCall()).getName().toString());
               printListOfCallTreesAsGraphviz(unterknoten);
            }
            catch (DebugException e) {
               e.printStackTrace();
            }
         }
      }
   }
}
