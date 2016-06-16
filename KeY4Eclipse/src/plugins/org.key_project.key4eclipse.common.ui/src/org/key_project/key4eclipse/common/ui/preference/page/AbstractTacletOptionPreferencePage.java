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
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.preference.IPreferencePage;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.*;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.PlatformUI;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.viewer.ButtonViewer;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.gui.configuration.TacletOptionSelector;
import de.uka.ilkd.key.gui.configuration.TacletOptionSelector.TacletOptionEntry;
import de.uka.ilkd.key.settings.TacletOptionSettings;

/**
 * Provides a basic {@link IPreferencePage} implementation to edit
 * {@link TacletOptionSettings}.
 * @author Martin Hentschel
 */
public abstract class AbstractTacletOptionPreferencePage extends PreferencePage implements IWorkbenchPreferencePage {
   /**
    * The {@link TacletOptionSettings} to edit.
    */
   private TacletOptionSettings choiceSettings;
   
   /**
    * Reference to {@link TacletOptionSettings#getDefaultTacletOptions()} of {@link #choiceSettings}.
    */
   private HashMap<String, String> category2DefaultTacletOption;
   
   /**
    * Reference to {@link TacletOptionSettings#getTacletOptions()} of {@link #choiceSettings}.
    */
   private HashMap<String, Set<String>> category2TacletOptions;
   
   /**
    * Maps the category to the {@link ButtonViewer} which allows the user to change the setting.
    */
   private Map<String, ButtonViewer> category2TacletOptionViewerMapping = new HashMap<String, ButtonViewer>();
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IWorkbench workbench) {
      if (isTacletOptionSettingsLoadingRequired()) {
         doLoadTacletOptionSettings();
      }
      choiceSettings = getTacletOptionSettings();
      category2DefaultTacletOption = choiceSettings.getDefaultTacletOptions();
      category2TacletOptions = choiceSettings.getTacletOptions();
   }
   
   /**
    * Checks if it is required to load the {@link TacletOptionSettings} or
    * if they are already available.
    * @return {@code true} load {@link TacletOptionSettings}, {@code false} {@link TacletOptionSettings} already available.
    */
   protected abstract boolean isTacletOptionSettingsLoadingRequired();

   /**
    * Loads the {@link TacletOptionSettings} if required in a different {@link Thread}
    * and shows the progress to the user in a dialog.
    */
   protected void doLoadTacletOptionSettings() {
      try {
         PlatformUI.getWorkbench().getProgressService().run(true, false, new IRunnableWithProgress() {
            @Override
            public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
               loadTacletOptionSettings(monitor);
            }
         });
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getControl() != null ? getShell() : null, e);
      }
   }
   
   /**
    * Loads the {@link TacletOptionSettings}.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws InvocationTargetException Occurred Exception.
    * @throws InterruptedException Occurred Exception.
    */
   protected abstract void loadTacletOptionSettings(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException;
   
   /**
    * Returns the {@link TacletOptionSettings} to edit.
    * @return The {@link TacletOptionSettings} to edit.
    */
   protected abstract TacletOptionSettings getTacletOptionSettings();

   /**
    * {@inheritDoc}
    */
   @Override
   protected Control createContents(Composite parent) {
      // Create root composite
      Composite rootComposite = new Composite(parent, SWT.NONE);
      rootComposite.setLayout(new GridLayout(1, false));
      // Create categories viewer
      TabFolder categoriesTabFolder = new TabFolder(rootComposite, SWT.NONE);
      categoriesTabFolder.setLayoutData(new GridData(GridData.FILL_BOTH));
      String[] categories = computeCategories(category2DefaultTacletOption);
      for (String category : categories) {
         TabItem categoryTabItem = new TabItem(categoriesTabFolder, SWT.NONE);
         categoryTabItem.setText(category);
         Composite tabComposite = new Composite(categoriesTabFolder, SWT.NONE);
         tabComposite.setLayout(new GridLayout(1, false));
         categoryTabItem.setControl(tabComposite);
         
         Group settingsGroup = new Group(tabComposite, SWT.NONE);
         settingsGroup.setText("Settings");
         settingsGroup.setLayout(new FillLayout());
         settingsGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
         ButtonViewer settingsViewer = new ButtonViewer(settingsGroup, SWT.RADIO);
         settingsViewer.setContentProvider(ArrayContentProvider.getInstance());
         TacletOptionEntry[] choices = TacletOptionSelector.createTacletOptionEntries(category2TacletOptions.get(category));
         settingsViewer.setInput(choices);
         settingsViewer.setSelection(SWTUtil.createSelection(TacletOptionSelector.findTacletOption(choices, category2DefaultTacletOption.get(category))));
         category2TacletOptionViewerMapping.put(category, settingsViewer);
         
         Group explanationGroup = new Group(tabComposite, SWT.NONE);
         explanationGroup.setText("Explanation");
         explanationGroup.setLayout(new FillLayout());
         explanationGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
         Text explanationText = new Text(explanationGroup, SWT.BORDER | SWT.MULTI | SWT.V_SCROLL | SWT.WRAP);
         explanationText.setEditable(false);
         String explanation = TacletOptionSelector.getExplanation(category);
         SWTUtil.setText(explanationText, StringUtil.trim(explanation));
      }
      return rootComposite;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected Point doComputeSize() {
      return new Point(0, 0);
   }

   /**
    * Computes the categories to show.
    * @param category2DefaultTacletOption The category to setting mapping.
    * @return The categories to show.
    */
   protected String[] computeCategories(HashMap<String, String> category2DefaultTacletOption) {
      Set<String> keys = category2DefaultTacletOption.keySet();
      String[] cats = keys.toArray(new String[keys.size()]);
      Arrays.sort(cats);
      return cats;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void performDefaults() {
      Map<String, String> defaults = getDefaults();
      if (defaults != null) {
         for (Entry<String, String> entry : defaults.entrySet()) {
            ButtonViewer viewer = category2TacletOptionViewerMapping.get(entry.getKey());
            if (viewer != null) { // Otherwise default value for not existing choice
               TacletOptionEntry[] choices = (TacletOptionEntry[])viewer.getInput();
               viewer.setSelection(SWTUtil.createSelection(TacletOptionSelector.findTacletOption(choices, entry.getValue())));
            }
         }
      }
   }
   
   /**
    * Returns the default values.
    * @return The default values.
    */
   public abstract Map<String, String> getDefaults();

   /**
    * {@inheritDoc}
    */
   @Override
   protected void performApply() {
      applyChanges();
      super.performApply();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performOk() {
      applyChanges();
      return super.performOk();
   }
   
   /**
    * Applies the values defined by the user in the UI to the edited {@link TacletOptionSettings}.
    */
   protected void applyChanges() {
      Set<Entry<String, ButtonViewer>> entries = category2TacletOptionViewerMapping.entrySet();
      for (Entry<String, ButtonViewer> entry : entries) {
         ISelection selection = entry.getValue().getSelection();
         Object selectedElement = SWTUtil.getFirstElement(selection);
         if (selectedElement instanceof TacletOptionEntry) {
            category2DefaultTacletOption.put(entry.getKey(), ((TacletOptionEntry)selectedElement).getTacletOption());
         }
      }
      choiceSettings.setDefaultTacletOptions(category2DefaultTacletOption);
   }
}