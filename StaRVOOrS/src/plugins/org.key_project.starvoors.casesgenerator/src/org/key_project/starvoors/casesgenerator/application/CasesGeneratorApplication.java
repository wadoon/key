package org.key_project.starvoors.casesgenerator.application;

import java.io.File;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;
import org.eclipse.swt.widgets.Display;
import org.key_project.starvoors.model.StaRVOOrSResult;
import org.key_project.starvoors.model.io.StaRVOOrSWriter;
import org.key_project.starvoors.util.StaRVOOrSUtil;
import org.key_project.ui.util.KeYExampleUtil;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The main entry point of the StaRVOOrS cases generator.
 * @author Jesus Mauricio Chimento
 */
public class CasesGeneratorApplication implements IApplication {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object start(IApplicationContext context) throws Exception {
      // Ensure that Eclipse 4 is ready
      while (Display.getDefault().readAndDispatch()) {
         Thread.sleep(10);
      }
      // Launch application
      String[] arguments = getStartArguments(context);
      if (arguments.length == 2) {
         File file = new File(arguments[0]);
         if (file.exists()) {
            System.out.println("Setting the taclet options...");
            setYDefaultTacletOptions();
            System.out.println("Analizing the contracts...");
            StaRVOOrSResult result;
            try {
                result = StaRVOOrSUtil.start(file);
            }
            catch (ProblemLoaderException e) {
                result = null;
                System.out.println("KeY has failed loading the files.");
            }
            
            if (result != null) {       
               System.out.println("Generating out.xml file...");
               String arg = arguments[1];
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
         System.out.println("The file to analyze and the path to the result file are expected as only parameter.");
      }
      return IApplication.EXIT_OK;
   }
   
   protected void setYDefaultTacletOptions() throws ProblemLoaderException {
      // Create and dispose proof required to set Taclet options
      KeYEnvironment<?> env = KeYEnvironment.load(KeYExampleUtil.getExampleProof(), null, null, null);
      env.dispose();
      // Set default taclet options
      ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
      HashMap<String, String> oldSettings = choiceSettings.getDefaultChoices();
      HashMap<String, String> newSettings = new HashMap<String, String>(oldSettings);
      newSettings.putAll(SymbolicExecutionUtil.getDefaultTacletOptions());
      choiceSettings.setDefaultChoices(newSettings);      
   }

   /**
    * Returns the start parameters if possible.
    * @param context The {@link IApplicationContext} to use.
    * @return The found start parameters or {@code null} if no one was found.
    */
   protected String[] getStartArguments(IApplicationContext context) {
       if (context != null) {
           Map<?, ?> arguments = context.getArguments();
           if (arguments != null) {
               Object value = arguments.get(IApplicationContext.APPLICATION_ARGS);
               return value instanceof String[] ? (String[])value : null;
           }
           else {
               return null;
           }
       }
       else {
           return null;
       }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void stop() {
   }
}
