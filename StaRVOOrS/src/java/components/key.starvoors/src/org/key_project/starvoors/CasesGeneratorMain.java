package org.key_project.starvoors;

import java.io.File;

import org.key_project.starvoors.model.StaRVOOrSResult;
import org.key_project.starvoors.model.io.StaRVOOrSWriter;
import org.key_project.starvoors.util.StaRVOOrSUtil;
import org.key_project.util.java.ArrayUtil;

import de.uka.ilkd.key.proof.io.ProblemLoaderException;

public class CasesGeneratorMain {
   public static final String INLINE_METHODS = "-inline";
   
   public static final String UNROLL_LOOPS = "-unroll";
   
   public static void main(String[] args) {
      try {
         run(args);
      }
      catch (Exception e) {
         e.printStackTrace();
      }
   }
   
   public static void run(String[] args) throws Exception {
      if (args.length >= 2) {
         File file = new File(args[0]);
         if (file.exists()) {
            boolean useOperationContracts = !ArrayUtil.contains(args, INLINE_METHODS);
            boolean useLoopInvarints = !ArrayUtil.contains(args, UNROLL_LOOPS);
            System.out.println("Setting the taclet options...");
            StaRVOOrSUtil.setDefaultTacletOptions(file);
            System.out.println("Analizing the contracts...");
            StaRVOOrSResult result;
            try {
                result = StaRVOOrSUtil.start(file, false, useOperationContracts, useLoopInvarints);
            }
            catch (ProblemLoaderException e) {
                result = null;
                System.out.println("KeY has failed loading the files.");
            }
            
            if (result != null) {       
               System.out.println("Generating out.xml file...");
               String arg = args[1];
               File resultFile;
               if (arg.charAt(arg.length()-1) == '/') {               
                  resultFile = new File(arg + "out.xml");                  
               } else {
                  resultFile = new File(arg + "/out.xml");                  
               }
               StaRVOOrSWriter.write(result, resultFile);
               System.out.println("\nProcess done.");
            } else {System.out.println("\nProcess Aborted.");}
            
         }
         else {
            System.out.println("The file \"" + file + "\" does not exist.");
         }
      }
      else {
         System.out.println("The file to analyze and the path to the result file are expected as first two parameters.");
         System.out.println();
         System.out.println("Additional parameters:");
         System.out.println(INLINE_METHODS + ": Inline method bodies instead of applying method contracts.");
         System.out.println(UNROLL_LOOPS + ": Unroll loops instead of applying loop invariants.");
      }
   }
}
