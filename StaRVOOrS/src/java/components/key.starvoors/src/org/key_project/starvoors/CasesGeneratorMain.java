package org.key_project.starvoors;

import java.io.File;

import org.key_project.starvoors.model.StaRVOOrSResult;
import org.key_project.starvoors.model.io.StaRVOOrSWriter;
import org.key_project.starvoors.util.StaRVOOrSUtil;
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
        String inputDir  = "", outputDir = "";
        boolean useOperationContracts = true, useLoopInvariants = true;
        File file,out;
        boolean input = true ;
        
		for (int i = 0; i < args.length; i++) {		
			if (args[i].equals("-inline"))
				useOperationContracts = false;
			
			if (args[i].equals("-unroll"))
				useLoopInvariants = false;
			
			if (input) {				
				inputDir = args[i];
			    input = false;
			} else {
				outputDir = args[i];
			}		
         }     	  
    	  
         file = new File(inputDir);
         out = new File(outputDir);
         
         if (!file.exists()) {
        	 System.out.println("The file \"" + file + "\" does not exist.");
        	 return;
         }         
         if (!out.exists()) {
        	 System.out.println("The folder \"" + out + "\" does not exist.");
        	 return;
         }
         
         System.out.println("Setting the taclet options for KeY...");
         try {
         StaRVOOrSUtil.setDefaultTacletOptions(file);
         } catch (ProblemLoaderException e) {   
             System.out.println("An error has occurred when setting the options:\n");
             System.out.println(e.getCause().toString());                
             return;
         }
            
         System.out.println("Analysing the Hoare triple(s)...");
         StaRVOOrSResult result;
         try {
             result = StaRVOOrSUtil.start(file, false, useOperationContracts, useLoopInvariants);
         }
         catch (ProblemLoaderException e) {
             result = null;
             System.out.println("KeY has failed loading the files.");
         }
            
         if (result != null) {    
            //Generating .xml file
            String arg = args[1];
            File resultFile;
            if (arg.charAt(arg.length()-1) == '/') {               
               resultFile = new File(arg + "out.xml");                  
            } else {
               resultFile = new File(arg + "/out.xml");                  
            }
            StaRVOOrSWriter.write(result, resultFile);
            System.out.println("\nStatic verification completed. See the generated report file for more details.");
         } else { System.out.println("\nStatic verification aborted."); }                  
         
      } else { usage(); }
   }
   
   public static void usage(){
	   System.out.println("Usage: java -jar key.starvoors.jar [-OPTIONS] <java_source_files> <output_path>");
       System.out.println();
       System.out.println("Options:");
       System.out.println(INLINE_METHODS + ": Inline method bodies instead of applying method contracts.");
       System.out.println(UNROLL_LOOPS + ": Unroll loops instead of applying loop invariants.");
   }
   
}
