package org.key_project.sed.extract_traces;

import java.io.File;
import java.util.HashMap;
import java.util.List;
import java.util.regex.Pattern;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.control.*;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.settings.*;
import de.uka.ilkd.key.symbolic_execution.*;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;
import de.uka.ilkd.key.symbolic_execution.po.ProgramMethodPO;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;
import de.uka.ilkd.key.symbolic_execution.util.*;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;


import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.Name;

/**
 * Example application which symbolically executes
 * {@code example/MaxIntBuggy}
 * Based on key.core.symbolic_execution.example
 * @author Lukas Grätz
 */
public class Main {
   /**
    * The program entry point.
    * @param args The start parameters.
    */
   public static void main(String[] args) {
      File location = new File("example"); // Path to the source code folder
      String className = "MaxIntBuggy";
      String methodName = "max";
      String[] methodArgTypes = {"int[]"};
      String preconditionGhostVar
         =    "(tc1 ==> arr.length == 4 && arr[0] == 2   && arr[1] == 1   && arr[2] == 3 && arr[3] == 4)"
         + "&& (tc2 ==> arr.length == 4 && arr[0] == 2   && arr[1] == 1   && arr[2] == 3 && arr[3] == 2)"
         + "&& (tc3 ==> arr.length == 3 && arr[0] == 0   && arr[1] == 1   && arr[2] == 3)"
         + "&& (tc4 ==> arr.length == 3 && arr[0] == 0   && arr[1] == 2   && arr[2] == 6)"
         + "&& (tc5 ==> arr.length == 3 && arr[0] == 2   && arr[1] == 4   && arr[2] == 3)"
         + "&& (tc6 ==> arr.length == 3 && arr[0] == 4   && arr[1] == 8   && arr[2] == 6)"
         + "&& (tc7 ==> arr.length == 3 && arr[0] == 200 && arr[1] == 400 && arr[2] == 300)"
         + "&& (tc8 ==> arr.length == 3 && arr[0] == 4   && arr[1] == 3   && arr[2] == 2)"
         + "&& (tc9 ==> arr.length == 3 && arr[0] == 550 && arr[1] == 4470&& arr[2] == 10)"
         + "&& (tc0 ==> arr.length == 3 && arr[0] == 200 >= arr[1] && arr[0] == arr[2])"
         + "&& (tc1 || tc2 || tc3 || tc4 || tc5 || tc6 || tc7 || tc8 || tc9 || tc0)"
//         + "&& (!tc1 || !tc2) && (!tc1 || !tc3) && (!tc1 || !tc4) && (!tc1 || !tc5) && (!tc2 || !tc3) && (!tc2 || !tc4) && (!tc2 || !tc5) && (!tc3 || !tc4) && (!tc3 || !tc5) && (!tc4 || !tc5)"
         + "&& arr != null";
      String preconditionQuantified
      =  "( \\exists int tc; 0 <= tc && tc <= 9;"
      +        "(tc == 1 ==> arr.length == 4 && arr[0] == 2   && arr[1] == 1   && arr[2] == 3 && arr[3] == 4)"
      +     "&& (tc == 2 ==> arr.length == 4                  && arr[1] == 1   && arr[2] == 3 && arr[3] == 2)"
      +     "&& (tc == 3 ==> arr.length == 3 && arr[0] == 0   && arr[1] == 1   && arr[2] == 3)"
      +     "&& (tc == 4 ==> arr.length == 3 && arr[0] == 0   && arr[1] == 2   && arr[2] == 6)"
      +     "&& (tc == 5 ==> arr.length == 3 && arr[0] == 2   && arr[1] == 4   && arr[2] == 3)"
      +     "&& (tc == 6 ==> arr.length == 3 && arr[0] == 4   && arr[1] == 8   && arr[2] == 6)"
      +     "&& (tc == 7 ==> arr.length == 3 && arr[0] == 200 && arr[1] == 400 && arr[2] == 300)"
      +     "&& (tc == 8 ==> arr.length == 3 && arr[0] == 4   && arr[1] == 3   && arr[2] == 2)"
      +     "&& (tc == 9 ==> arr.length == 3 && arr[0] == 550 && arr[1] == 4470&& arr[2] == 10)"
      +     "&& (tc == 0 ==> arr.length == 3 && arr[0] == 200 >= arr[1] && arr[0] == arr[2])"
      +  ")"
      + "&& arr != null";

      SymbolicExecutionTreeBuilder treeBuilder =null;

      try {
         treeBuilder = executeMethod(location, className, methodName, methodArgTypes, preconditionQuantified, null, null, null);
         System.out.println("Finished building SE tree");
         printSymbolicExecutionTree("", treeBuilder);
      } catch (ProofInputException e) {
         System.out.println("Exception at '" + location + "':");
         e.printStackTrace();
      } catch (ProblemLoaderException e) {
         System.out.println("Exception at '" + location + "':");
         e.printStackTrace();
      }
   }


   /**
    * Builds a symbolic execution tree for a given method
    * @param location Path to the source code folder
    * @param className Name of the class containing the method
    * @param methodName Method name
    * @param methodArgTypes An array of fully qualified names for each argument types,
    * e.g. "java.lang.String", "int[]" ...
    * @param precondition Optionally: JML precondition
    * @param classPaths Optionally: Additional specifications for API classes
    * @param bootClassPath Optionally: Different default specifications for Java API
    * @param includes Optionally: Additional includes to consider
    * @returns The symbolic execution tree builder
    * @throws ProblemLoaderException Exception in loading method
    * @throws ProofInputException 
    */
   public static SymbolicExecutionTreeBuilder executeMethod (File location, String className, String methodName, String[] methodArgTypes, String precondition, List<File> classPaths, File bootClassPath, List<File> includes) throws ProblemLoaderException, ProofInputException {
       SymbolicExecutionTreeBuilder builder;
       // Ensure that Taclets are parsed
       if (!ProofSettings.isChoiceSettingInitialised()) {
            KeYEnvironment<?> env = KeYEnvironment.load(location, classPaths, bootClassPath, includes);
            env.dispose();
       }
       // Set Taclet options
       ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
       HashMap<String, String> oldSettings = choiceSettings.getDefaultChoices();
       HashMap<String, String> newSettings = new HashMap<String, String>(oldSettings);
       newSettings.putAll(MiscTools.getDefaultTacletOptions());
       choiceSettings.setDefaultChoices(newSettings);
       // Load source code
       SymbolicExecutionJavaProfile profile = SymbolicExecutionJavaProfile.getDefaultInstance();
       KeYEnvironment<DefaultUserInterfaceControl> env =
             KeYEnvironment.load(profile, location, classPaths, bootClassPath, includes, true);
       
          // Find method to symbolically execute
          KeYJavaType classType = env.getJavaInfo().getKeYJavaType(className);
          ImmutableList<Type> signature = ImmutableSLList.<Type>nil();
          for (String t : methodArgTypes) {
             KeYJavaType keyType = env.getJavaInfo().getKeYJavaType(t);
             signature.append(keyType);
          }
          IProgramMethod pm = env.getJavaInfo().getProgramMethod(classType, methodName, signature, classType);
          
          // Instantiate proof for symbolic execution of the program method (Java semantics)
          AbstractOperationPO po = new ProgramMethodPO(env.getInitConfig(), 
                                                       "Symbolic Execution of: " + pm, 
                                                       pm, 
                                                       precondition,
                                                       true,
                                                       true);

          Proof proof = env.createProof(po);
          // Create symbolic execution tree builder
          builder = new SymbolicExecutionTreeBuilder(proof, 
                                                     false, // Merge branch conditions 
                                                     false, // Use Unicode? 
                                                     true, // Use Pretty Printing? 
                                                     true, // Variables are collected from updates instead of the visible type structure 
                                                     true); // Simplify conditions
          builder.analyse();
          // Optionally, create an SymbolicExecutionEnvironment which provides access to all relevant objects for symbolic execution
          SymbolicExecutionEnvironment<DefaultUserInterfaceControl> symbolicEnv = new SymbolicExecutionEnvironment<DefaultUserInterfaceControl>(env, builder);
          // Configure strategy for full exploration
          SymbolicExecutionUtil.initializeStrategy(builder);
          SymbolicExecutionEnvironment.configureProofForSymbolicExecution(proof, 
                                                                          100, 
                                                                          false,  // true to apply method contracts instead of inlining, 
                                                                          false,  // true to apply loop invariants instead of unrolling, 
                                                                          false,  // true to apply block contracts instead of expanding.
                                                                          false,  // true to hide branch conditions caused by symbolic execution within modalities not of interest, 
                                                                          false); // true to perform alias checks during symbolic execution
          // Perform strategy which will stop at breakpoint
          symbolicEnv.getProofControl().startAndWaitForAutoMode(proof);
          builder.analyse();
          
          // FIXME Ensure always that all instances of KeYEnvironment are disposed
          // env.dispose();
       return builder;
   }

   /**
    * Prints the symbolic execution tree into the console.
    * @param title The title.
    * @param builder The {@link SymbolicExecutionTreeBuilder} providing the root of the symbolic execution tree.
    * @throws ProofInputException 
    */
   protected static void printSymbolicExecutionTree(String title, SymbolicExecutionTreeBuilder builder) throws ProofInputException {
      System.out.println(title);
      System.out.println(StringUtil.createLine("=", title.length()));
      IExecutionStart startNode = builder.getStartNode();
      printSEDhierarchy(startNode, 0, true);
   }

   /**
    * Prints the symbolic execution tree tree to the console
    * @param node root of the sub tree
    * @param level start with 0, increment for each branch
    * @param plus true to print a + for branching
    * @throws ProofInputException
    */
   protected static void printSEDhierarchy (IExecutionNode<?> node, int level, boolean plus) throws ProofInputException {
      StringBuilder builder = new StringBuilder();
      String name;
      for(int i = 0; i < level; i++) {
         builder.append("|  ");
      }
      if (plus) {
         builder.append("+ ");
         plus = false;
      } else {
         builder.append("| ");
      }
      if (node instanceof IExecutionMethodReturn) {
         name = (((IExecutionMethodReturn) node).isReturnValuesComputed() || !node.isDisposed())
              ? ((IExecutionMethodReturn) node).getNameIncludingReturnValue()
              : node.getName();
      } else {
         name = node.getName();
      }
//      name = node.toString();
      // removes unnecessary << >> and \n (FIXME better solution)
      name = name.replaceAll("(<<.*?>>)|(«.*?»)","");
      name = name.replaceAll("[\t ]*\n[\t ]*", " ");
      builder.append(name);
      System.out.println(builder);

      IExecutionNode<?>[] children = node.getChildren();
      if (children.length != 1) {
         level++;
         plus = true;
      }
      for (IExecutionNode<?> child : node.getChildren()) {
         printSEDhierarchy(child, level, plus);
      }
   }
}
