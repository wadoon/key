package org.key_project.starvoors.casesgenerator.application;

import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;

public class CasesGenerator implements IApplication {

   @Override
   public Object start(IApplicationContext context) throws Exception {
      System.out.println("Hello WOrld!");
      return IApplication.EXIT_OK;
   }

   @Override
   public void stop() {
   }
}
