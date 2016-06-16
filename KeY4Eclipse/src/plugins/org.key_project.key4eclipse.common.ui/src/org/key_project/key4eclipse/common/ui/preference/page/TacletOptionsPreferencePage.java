/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.key4eclipse.common.ui.preference.page;

import java.lang.reflect.InvocationTargetException;
import java.util.Map;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.ui.IWorkbench;
import org.key_project.ui.util.KeYExampleUtil;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.settings.TacletOptionSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Preference page to edit the taclet options.
 * @author Martin Hentschel
 */
public class TacletOptionsPreferencePage extends AbstractTacletOptionPreferencePage {
   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IWorkbench workbench) {
      super.init(workbench);
      setMessage("Changes will become effective when the next problem is loaded.", IMessageProvider.INFORMATION);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean isTacletOptionSettingsLoadingRequired() {
      return !SymbolicExecutionUtil.isChoiceSettingInitialised();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void loadTacletOptionSettings(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
      try {
         monitor.beginTask("Computing Taclet Options", IProgressMonitor.UNKNOWN);
         loadTacletOptionSettings();
      }
      catch (Exception e) {
         throw new InvocationTargetException(e, e.getMessage());
      }
      finally {
         monitor.done();
      }
   }
   
   /**
    * Loads the proof specified by {@link #getExampleProof()} to make sure
    * that {@link ChoiceSettings} are loaded.
    * @throws ProblemLoaderException
    */
   public static void loadTacletOptionSettings() throws ProblemLoaderException {
      KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(KeYExampleUtil.getExampleProof(), null, null, null);
      env.dispose();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected TacletOptionSettings getTacletOptionSettings() {
      return ProofSettings.DEFAULT_SETTINGS.getTacletOptionSettings();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Map<String, String> getDefaults() {
      return getDefaultTacletOptions();
   }
   
   /**
    * Returns the default taclet options.
    * @return The default taclet options.
    */
   public static Map<String, String> getDefaultTacletOptions() {
      return SymbolicExecutionUtil.getDefaultTacletOptions();
   }
}