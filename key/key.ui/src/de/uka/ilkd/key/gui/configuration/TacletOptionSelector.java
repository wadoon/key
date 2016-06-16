// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.configuration;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.HashMap;
import java.util.InvalidPropertiesFormatException;
import java.util.Properties;
import java.util.Set;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JList;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.KeyStroke;
import javax.swing.ListSelectionModel;
import javax.swing.ScrollPaneConstants;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.settings.TacletOptionSettings;
import de.uka.ilkd.key.settings.ProofSettings;

public class TacletOptionSelector extends JDialog {

    /**
     * 
     */
    private static final long serialVersionUID = -4470713015801365801L;
    private static final String EXPLANATIONS_RESOURCE = "/de/uka/ilkd/key/gui/help/choiceExplanations.xml";
    private TacletOptionSettings settings;
    private HashMap<String, String> category2DefaultChoice;
    private HashMap<String, Set<String>> category2Choices;
    private boolean changed=false;


    /** the JList with the categories of choices*/
    private JList<String> catList;
    /** the JList with the choices for one category */
    private JList<TacletOptionEntry> choiceList;
    private JTextArea explanationArea;
    private static Properties explanationMap;

    /** creates a new TacletOptionSelector, using the <code>TacletOptionSettings</code>
     * from <code>settings</code> */
    public TacletOptionSelector(TacletOptionSettings settings) {  
	super(new JFrame(), "Taclet Base Configuration", true);
       	this.settings = settings;
	category2DefaultChoice = settings.getDefaultTacletOptions();
	if(category2DefaultChoice.isEmpty()) {
	    JOptionPane.showConfirmDialog
		(TacletOptionSelector.this,
		 "There are no Taclet Options available as the rule-files "+
		 "have not been parsed yet!",
		 "No Options available", 
		 JOptionPane.DEFAULT_OPTION);
	    dispose();
	} else {
	    category2Choices = settings.getTacletOptions();
	    layoutChoiceSelector();
	    setChoiceList();
	    pack();
	    setLocationRelativeTo(null);
	    //setLocation(70, 70);
	    setVisible(true);
	}
    }

    /** creates a new TacletOptionSelector */
    public TacletOptionSelector(){
	this(ProofSettings.DEFAULT_SETTINGS.getTacletOptionSettings());
    }

    /** layout */
    protected void layoutChoiceSelector() {
        setIconImage(IconFactory.keyLogo());
        JPanel listPanel=new JPanel();
        listPanel.setLayout(new BorderLayout());
        String[] cats = category2DefaultChoice.keySet().toArray(new String[category2DefaultChoice.size()]);
        Arrays.sort(cats);
        {
            catList = new JList<>(cats);
            catList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
            catList.setSelectedIndex(0);
            catList.addListSelectionListener(new ListSelectionListener() {
                public void valueChanged(ListSelectionEvent e) {
                    setChoiceList();				
                }});
            JScrollPane catListScroll = new
                    JScrollPane(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED, 
                            ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
            catListScroll.setBorder(new TitledBorder("Category"));
            catListScroll.getViewport().setView(catList);
            Dimension paneDim = new Dimension(200, 300);
            catListScroll.setPreferredSize(paneDim);
            catListScroll.setMinimumSize(paneDim);
            listPanel.add(catListScroll, BorderLayout.WEST);
        }
        {
            choiceList = new JList<>();
            choiceList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
            choiceList.setSelectedValue(category2DefaultChoice.get(cats[0]),true);
            choiceList.addListSelectionListener(new ListSelectionListener() {
                public void valueChanged(ListSelectionEvent e) {
                    Object selectedValue = choiceList.getSelectedValue();
                    if (selectedValue instanceof TacletOptionEntry) {
                       setDefaultChoice(((TacletOptionEntry) selectedValue).getTacletOption());
                    }
                    else {
                       setDefaultChoice(null);
                    }
                }});

            JScrollPane choiceScrollPane = new 	    
                    JScrollPane(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED, 
                            ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
            choiceScrollPane.getViewport().setView(choiceList);
            choiceScrollPane.setBorder(new TitledBorder("TacletOption"));
            Dimension paneDim = new Dimension(300, 300);
            choiceScrollPane.setPreferredSize(paneDim);
            choiceScrollPane.setMinimumSize(paneDim);
            listPanel.add(choiceScrollPane, BorderLayout.EAST);
        }
        {
            explanationArea = new JTextArea("Explanation!");
            explanationArea.setEditable(false);
            explanationArea.setLineWrap(true);
            explanationArea.setWrapStyleWord(true);
            JScrollPane scrollPane = new JScrollPane(explanationArea);
            Dimension paneDim = new Dimension(500, 200);
            scrollPane.setPreferredSize(paneDim);
            scrollPane.setMinimumSize(paneDim);
            listPanel.add(scrollPane, BorderLayout.SOUTH);
        }
        JPanel buttonPanel = new JPanel();
        {
            JButton ok = new JButton("OK");
            ok.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    if(changed){
                        int res = JOptionPane.showOptionDialog
                                (TacletOptionSelector.this,
                                        "Your changes will become effective when "+
                                                "the next problem is loaded.\n", 
                                                "Taclet Options", 
                                                JOptionPane.DEFAULT_OPTION,
                                                JOptionPane.QUESTION_MESSAGE, null,
                                                new Object[]{"OK", "Cancel"}, "OK");
                        if (res==0){
                            settings.setDefaultTacletOptions(
                                    category2DefaultChoice);
                        }
                    }
                    setVisible(false);
                    dispose();
                }
            });
            buttonPanel.add(ok);
            getRootPane().setDefaultButton(ok);	
        }
        {
            final JButton cancel = new JButton("Cancel");
            cancel.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    setVisible(false);
                    dispose();
                }
            });
            ActionListener escapeListener = new ActionListener() {
                public void actionPerformed(ActionEvent event) {
                    if(event.getActionCommand().equals("ESC")) {
                        cancel.doClick();
                    }
                }
            };
            cancel.registerKeyboardAction(
                    escapeListener,
                    "ESC",
                    KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0),
                    JComponent.WHEN_IN_FOCUSED_WINDOW);	
            buttonPanel.add(cancel);
        }

	getContentPane().setLayout(new BorderLayout());
	getContentPane().add(listPanel, BorderLayout.CENTER);
	getContentPane().add(buttonPanel, BorderLayout.SOUTH);
	
	setResizable(false);
    }


    /** is called to set the selected choice in 
     * <code>category2DefaultChoice</code>*/
    private void setDefaultChoice(String sel) {
	String category = (String) catList.getSelectedValue();
	if(sel != null){
	    category2DefaultChoice.put(category,sel);
	    changed = true;
	}
    }

    /** is called if the selection of left list has changed, and causes the
     * right one to display the possible choices for the category chosen on
     * the left side
     */
    private void setChoiceList() {
	String selection = (String) catList.getSelectedValue();
	TacletOptionEntry[] choices = createTacletOptionEntries(category2Choices.get(selection));
	choiceList.setListData(choices);
	TacletOptionEntry selectedChoice = findTacletOption(choices, category2DefaultChoice.get(selection));
	choiceList.setSelectedValue(selectedChoice, false);
	explanationArea.setBorder(BorderFactory.createTitledBorder(selection));
	explanationArea.setText(getExplanation(selection));
	explanationArea.setCaretPosition(0);
    }

   /**
     * <p>
     * Returns the explanation for the given category.
     * </p>
     * <p>
     * This method should be public and static because it is independent
     * from the {@link JDialog} and it is also used by the eclipse projects.
     * </p>
     * @param category The category for which the explanation is requested.
     * @return The explanation for the given category.
     */
    public static String getExplanation(String category) {
        synchronized (TacletOptionSelector.class) {
            if(explanationMap == null) {
                explanationMap = new Properties();
                InputStream is = TacletOptionSelector.class.getResourceAsStream(EXPLANATIONS_RESOURCE);
                try {
                    if (is == null) {
                        throw new FileNotFoundException(EXPLANATIONS_RESOURCE + " not found");
                    }
                    explanationMap.loadFromXML(is);
                } catch (InvalidPropertiesFormatException e) {
                    System.err.println("Cannot load help message in rule view (malformed XML).");
                    e.printStackTrace();
                } catch (IOException e) {
                    System.err.println("Cannot load help messages in rule view.");
                    e.printStackTrace();
                } 
            }
        }
        String result = explanationMap.getProperty(category);
        if(result == null) {
            result = "No explanation for " + category + " available.";
        }
        
        return result;
    }
    
    /**
     * Checks if the given choice makes a proof unsound.
     * @param choice The choice to check.
     * @return {@code true} proof will be unsound, {@code false} proof will be sound as long as all other choices are sound.
     */
    public static boolean isUnsound(String choice) {
       return "runtimeExceptions:ignore".equals(choice) ||
              "initialisation:disableStaticInitialisation".equals(choice) ||
              "intRules:arithmeticSemanticsIgnoringOF".equals(choice);
    }
    
    /**
     * Checks if the given choice makes a proof incomplete.
     * @param choice The choice to check.
     * @return {@code true} proof will be incomplete, {@code false} proof will be complete as long as all other choices are complete.
     */
    public static boolean isIncomplete(String choice) {
       return "runtimeExceptions:ban".equals(choice) ||
              "Strings:off".equals(choice) ||
              "intRules:arithmeticSemanticsCheckingOF".equals(choice) ||
              "integerSimplificationRules:minimal".equals(choice) ||
              "programRules:None".equals(choice);
    }
    
    /**
     * Checks if additional information for the choice are available.
     * @param choice The choice to check.
     * @return The additional information or {@code null} if no information are available.
     */
    public static String getInformation(String choice) {
       if ("JavaCard:on".equals(choice)) {
          return "Sound if a JavaCard program is proven.";
       }
       else if ("JavaCard:off".equals(choice)) {
          return "Sound if a Java program is proven.";
       }
       else if ("assertions:on".equals(choice)) {
          return "Sound if JVM is started with enabled assertions for the whole system.";
       }
       else if ("assertions:off".equals(choice)) {
          return "Sound if JVM is started with disabled assertions for the whole system.";
       }
       else {
          return null;
       }
    }

    /**
     * Searches the taclet option in the given {@link TacletOptionEntry}s.
     * @param tacletOptions The {@link TacletOptionEntry}s to search in.
     * @param tacletOption The taclet option to search.
     * @return The found {@link TacletOptionEntry} for the given choice or {@code null} otherwise.
     */
    public static TacletOptionEntry findTacletOption(TacletOptionEntry[] tacletOptions, final String tacletOption) {
       return ArrayUtil.search(tacletOptions, new IFilter<TacletOptionEntry>() {
         @Override
         public boolean select(TacletOptionEntry element) {
            return element.getTacletOption().equals(tacletOption);
         }
       });
    }

    /**
     * Creates {@link TacletOptionEntry}s for all given taclet options.
     * @param tacletOptions The taclet options.
     * @return The created {@link TacletOptionEntry}s.
     */
    public static TacletOptionEntry[] createTacletOptionEntries(Set<String> tacletOptions) {
       if (tacletOptions != null) {
          TacletOptionEntry[] entries = new TacletOptionEntry[tacletOptions.size()];
          int i = 0;
          for (String choice : tacletOptions) {
             entries[i] = createTacletOptionEntry(choice);
             i++;
          }
          return entries;
       }
       else {
          return null;
       }
    }

    /**
     * Creates a {@link TacletOptionEntry} for the given choice.
     * @param tacletOption The choice.
     * @return The created {@link TacletOptionEntry}.
     */
    public static TacletOptionEntry createTacletOptionEntry(String tacletOption) {
       return new TacletOptionEntry(tacletOption, 
                              isUnsound(tacletOption), 
                              isIncomplete(tacletOption), 
                              getInformation(tacletOption));
    }
    
   /**
    * Represents a choice with all its meta information.
    * @author Martin Hentschel
    */
   public static class TacletOptionEntry {
      /**
       * Text shown to the user in case of incompletness.
       */
      public static final String INCOMPLETE_TEXT = "incomplete";
      
      /**
       * Text shown to the user in case of unsoundness.
       */
      public static final String UNSOUND_TEXT = "Java modeling unsound";
      
      /**
       * The choice.
       */
      private final String tacletOption;

      /**
       * Is unsound?
       */
      private final boolean unsound;

      /**
       * Is incomplete?
       */
      private final boolean incomplete;
      
      /**
       * An optionally information.
       */
      private final String information;

      /**
       * Constructor.
       * @param tacletOption The taclet option.
       * @param unsound Is unsound?
       * @param incomplete Is incomplete?
       * @param information An optionally information.
       */
      public TacletOptionEntry(String tacletOption, boolean unsound, boolean incomplete, String information) {
         assert tacletOption != null;
         this.tacletOption = tacletOption;
         this.unsound = unsound;
         this.incomplete = incomplete;
         this.information = information;
      }

      /**
       * Returns the taclet option.
       * @return The taclet option.
       */
      public String getTacletOption() {
         return tacletOption;
      }

      /**
       * Checks for soundness.
       * @return {@code true} unsound, {@code false} sound.
       */
      public boolean isUnsound() {
         return unsound;
      }

      /**
       * Checks for completeness.
       * @return {@code true} incomplete, {@code false} complete.
       */
      public boolean isIncomplete() {
         return incomplete;
      }

      /**
       * Returns the optionally information.
       * @return The optionally information.
       */
      public String getInformation() {
         return information;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public int hashCode() {
         int hashcode = 5;
         hashcode = hashcode * 17 + tacletOption.hashCode();
         hashcode = hashcode * 17 + (incomplete ? 5 : 3);
         hashcode = hashcode * 17 + (unsound ? 5 : 3);
         if (information != null) {
            hashcode = hashcode * 17 + information.hashCode();          
         }
         return hashcode;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean equals(Object obj) {
         if (obj instanceof TacletOptionEntry) {
            TacletOptionEntry other = (TacletOptionEntry)obj;
            return tacletOption.equals(other.getTacletOption()) &&
                   incomplete == other.isIncomplete() &&
                   unsound == other.isUnsound() &&
                   ObjectUtil.equals(information, other.getInformation());
         }
         else {
            return false;
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String toString() {
         if (unsound && incomplete) {
            if (information != null) {
               return tacletOption + " (" + UNSOUND_TEXT + " and " + INCOMPLETE_TEXT + ", " + information + ")";
            }
            else {
               return tacletOption + " (" + UNSOUND_TEXT + " and " + INCOMPLETE_TEXT + ")";
            }
         }
         else if (unsound) {
            if (information != null) {
               return tacletOption + " (" + UNSOUND_TEXT + ", " + information + ")";
            }
            else {
               return tacletOption + " (" + UNSOUND_TEXT + ")";
            }
         }
         else if (incomplete) {
            if (information != null) {
               return tacletOption + " (" + INCOMPLETE_TEXT + ", " + information + ")";
            }
            else {
               return tacletOption + " (" + INCOMPLETE_TEXT + ")";
            }
         }
         else {
            if (information != null) {
               return tacletOption + " (" + information + ")";
            }
            else {
               return tacletOption;
            }
         }
      }
   }
}