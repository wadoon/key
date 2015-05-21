package org.key_project.starvoors.casesgenerator.application;

import java.util.Map;

import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;
import org.eclipse.swt.widgets.Display;
import org.key_project.starvoors.CasesGeneratorMain;

/**
 * The main entry point of the StaRVOOrS cases generator.
 * The
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
      CasesGeneratorMain.run(arguments);
      return IApplication.EXIT_OK;
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
