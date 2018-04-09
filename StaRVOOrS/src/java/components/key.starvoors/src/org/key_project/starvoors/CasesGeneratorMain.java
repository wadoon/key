package org.key_project.starvoors;

import java.io.File;

import org.key_project.starvoors.model.StaRVOOrSResult;
import org.key_project.starvoors.model.io.StaRVOOrSWriter;
import org.key_project.starvoors.util.StaRVOOrSUtil;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;


public class CasesGeneratorMain {
   public static final String INLINE_METHODS = "-inline";
   
   public static final String UNROLL_LOOPS = "-unroll";
   
   public static final String JAVA_DL = "-javadl";
   
   public static void main(String[] args) {
      try {
    	  if (args.length >= 2) {
    		  boolean mode = true;
    		  
    		  for(String arg : args) {
    			  if (arg.equals("-javadl"))
    				  mode = false;
    		  }
    		  if (mode)
    			  run(args);   
    		  else { run_javadl(args); }
    	  } else {
    		  usage();
    	  }
      }
      catch (Exception e) {
         e.printStackTrace();
      }
   }
   
   //Runs KeY in Java files with JML contracts annotated
   public static void run(String[] args) throws Exception {	   
        String inputDir  = "", outputDir = "";
        boolean useOperationContracts = true, useLoopInvariants = true;
        File file,out;
        boolean input = true ;
        
		for (int i = 0; i < args.length; i++) {		
			if (args[i].equals("-inline")) {
				useOperationContracts = false;
				continue;
			}			
			if (args[i].equals("-unroll")) {
				useLoopInvariants = false;
				continue;
			}			
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
            File resultFile;
            if (outputDir.charAt(outputDir.length()-1) == '/') {               
               resultFile = new File(outputDir + "out.xml");                  
            } else {
               resultFile = new File(outputDir + "/out.xml");                  
            }
            StaRVOOrSWriter.write(result, resultFile);
            System.out.println("\nVerification completed. See the generated report file for more details.");
         } else { System.out.println("\nVerification aborted."); }                  
   }
   
   //Runs KeY in files containing dynamic logic formulae.
   public static void run_javadl(String[] args) throws Exception {
        String inputDir  = "", outputDir = "", formulae = "";
        File file,out,formulas;
        boolean input = true, output = true ;
       
		for (int i = 0; i < args.length; i++) {		
			if (args[i].equals("-inline")) {
				continue;
			}			
			if (args[i].equals("-unroll")) {
				continue;
			}			
			if (args[i].equals("-javadl")) {
				continue;
			}			
			if (input) {				
				inputDir = args[i];
			    input = false;
			} else {
				if (output) {
     				outputDir = args[i];
     				output = false;
     			} else {
     				formulae = args[i];
     			}
			}		
        }     	  
   	  
        file = new File(inputDir);
        out = new File(outputDir);
        formulas = new File(formulae);
        
        if (!file.exists()) {
           System.out.println("The file \"" + file + "\" does not exist.");
           return;
        }         
        if (!out.exists()) {
           System.out.println("The folder \"" + out + "\" does not exist.");
           return;
        }
        if (!formulas.exists()) {
           System.out.println("The file \"" + formulas + "\" does not exist.");
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
           
        System.out.println("Analysing the Java Dynamic Logic formula(e)...");
        StaRVOOrSResult result;
        try {
        	//TODO: Create new start method to analyse dynamic logic formulae.
            result = StaRVOOrSUtil.start_javadl(file, formulas, false);
        }
        catch (ProblemLoaderException e) {
            result = null;
            System.out.println("KeY has failed loading the files.");
        }
           
        if (result != null) {    
           //Generating .xml file
           File resultFile;
           if (outputDir.charAt(outputDir.length()-1) == '/') {               
               resultFile = new File(outputDir + "out.xml");
            } else {
               resultFile = new File(outputDir + "/out.xml");
            }
           //TODO: Create new writer method for dynamic logic formulae analysis.
           StaRVOOrSWriter.write(result, resultFile);
           System.out.println("\nVerification completed. See the generated report file for more details.");
        } else { System.out.println("\nVerification aborted."); } 
   }
   
   public static void usage(){
	   System.out.println("Usage: java -jar key.starvoors.jar [-OPTIONS] <java_source_files> <output_path>");
       System.out.println();
       System.out.println("Options:");
       System.out.println(INLINE_METHODS + ": Inline method bodies instead of applying method contracts.");
       System.out.println(UNROLL_LOOPS + ": Unroll loops instead of applying loop invariants.");
       System.out.println(JAVA_DL + ": File(s) to analyse contain(s) (Java) dynamic logic formulae. Folder to formulae should be included as the final argument.");
   }
   
}
