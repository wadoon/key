package de.uka.ilkd.keyabs.gui;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.init.proofobligations.ABSAbstractPO;
import de.uka.ilkd.key.proof.init.proofobligations.ABSPreservesInvariantPO;
import de.uka.ilkd.key.ui.UserInterface;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.proof.init.ABSInitConfig;
import de.uka.ilkd.keyabs.proof.init.ABSProblemInitializer;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ArrayList;
import java.util.StringTokenizer;

/**
 * Created with IntelliJ IDEA.
 * User: bubel
 * Date: 24.03.13
 * Time: 10:28
 * To change this template use File | Settings | File Templates.
 */
public class ProofObligationChooser {
    private static final String PRESERVES_INV_DISPLAY_TEXT = "Preserve Class Invariant";
    private final KeYMediator<ABSServices, ABSInitConfig> mediator;
    private final ABSInitConfig initConfig;

    private JList<Name> classes;
    private JList<POBrowserData.MethodRepresentative> methods;
    private JButton cancelButton;
    private JButton OKButton;
    private JList proofObligation;
    private JPanel browser;
    private POBrowserData data;
    private String selectedPO;

    public boolean isProofStarted() {
        return proofStarted;
    }

    private boolean proofStarted = false;


    public ProofObligationChooser(KeYMediator<ABSServices, ABSInitConfig> mediator,
                                  ABSInitConfig initConfig,
                                  POBrowserData data) {

        this.mediator = mediator;
        this.initConfig = initConfig;
        setData(data);

        classes.addListSelectionListener(new ListSelectionListener() {
            @Override
            public void valueChanged(ListSelectionEvent e) {
                final Name selectedClass = classes.getSelectedValue();
                methods.setListData(ProofObligationChooser.this.data.getMethods(selectedClass));
                if (methods.getModel().getSize() > 0) {
                    methods.setSelectedIndex(0);
                }
            }
        });
        methods.addListSelectionListener(new ListSelectionListener() {
            @Override
            public void valueChanged(ListSelectionEvent e) {
                ArrayList<String> poList = new ArrayList<>();
                if (methods.getSelectedValue() != null) {
                    boolean invariants = ProofObligationChooser.this.data.hasClassInvariantFor(classes.getSelectedValue());
                    if (invariants) {
                        poList.add(PRESERVES_INV_DISPLAY_TEXT);
                    }
                }
                proofObligation.setListData(poList.toArray());
                if (methods.getSelectedValue() != null &&
                        proofObligation.getModel().getSize() > 0) {
                    proofObligation.setSelectedIndex(0);
                }
            }
        });

        proofObligation.addListSelectionListener(new ListSelectionListener() {
            @Override
            public void valueChanged(ListSelectionEvent e) {
                if (proofObligation.getSelectedValue() != null) {
                    if (proofObligation.
                            getSelectedValue().equals(PRESERVES_INV_DISPLAY_TEXT)) {
                        selectedPO = ABSPreservesInvariantPO.PRESERVES_INV_PO;
                    }
                } else {
                    selectedPO = "";
                }
            }
        });


        final JDialog dialog = new JDialog((Dialog) null, "Proof-Obligation Browser", true);

        cancelButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                selectedPO = "";
                dialog.setVisible(false);
                dialog.dispose();
            }
        });

        OKButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {

                dialog.setVisible(false);
                dialog.dispose();

                if (selectedPO != null && !selectedPO.isEmpty()) {
                    StringTokenizer tokenize = new StringTokenizer(selectedPO, "::");
                    assert tokenize.countTokens() == 3;
                    tokenize.nextElement();
                    ABSAbstractPO po =
                            new ABSPreservesInvariantPO(ProofObligationChooser.this.initConfig,
                                    classes.getSelectedValue(), methods.getSelectedValue().getMethod());
                    findOrStartProof(po);
                    proofStarted = true;
                }
            }
        });

        dialog.getContentPane().add(browser);
        dialog.setModal(true);
        dialog.pack();
        dialog.setVisible(true);


    }

    private void findOrStartProof(ProofOblInput po) {
        UserInterface ui = mediator.getUI();
        AbstractProblemInitializer pi =
                new ABSProblemInitializer(ui,
                        mediator.getProfile(),
                        initConfig.getServices(), true, ui);
        try {
            pi.startProver(initConfig, po, 0);
        } catch (ProofInputException exc) {
        	exc.printStackTrace();
            ExceptionDialog.showDialog(MainWindow.getInstance(), exc);
        }
    }

    private void createUIComponents() {
        // TODO: place custom component creation code here
    }

    public void setData(POBrowserData data) {
        this.data = data;
        classes.setListData(data.getClasses());
        browser.repaint();
    }

    public void getData(POBrowserData data) {
    }

    public boolean isModified(POBrowserData data) {
        return false;
    }

    public String getSelectedPO() {
        return selectedPO;
    }

    {
// GUI initializer generated by IntelliJ IDEA GUI Designer
// >>> IMPORTANT!! <<<
// DO NOT EDIT OR ADD ANY CODE HERE!
        $$$setupUI$$$();
    }

    /**
     * Method generated by IntelliJ IDEA GUI Designer
     * >>> IMPORTANT!! <<<
     * DO NOT edit this method OR call it in your code!
     *
     * @noinspection ALL
     */
    private void $$$setupUI$$$() {
        browser = new JPanel();
        browser.setLayout(new GridBagLayout());
        browser.setBorder(BorderFactory.createTitledBorder(BorderFactory.createLoweredBevelBorder(), null, TitledBorder.DEFAULT_JUSTIFICATION, TitledBorder.DEFAULT_POSITION, new Font(browser.getFont().getName(), browser.getFont().getStyle(), browser.getFont().getSize()), new Color(-16777216)));
        final JPanel panel1 = new JPanel();
        panel1.setLayout(new GridBagLayout());
        GridBagConstraints gbc;
        gbc = new GridBagConstraints();
        gbc.gridx = 0;
        gbc.gridy = 1;
        gbc.gridwidth = 3;
        gbc.weightx = 1.0;
        gbc.anchor = GridBagConstraints.EAST;
        gbc.fill = GridBagConstraints.VERTICAL;
        browser.add(panel1, gbc);
        cancelButton = new JButton();
        cancelButton.setText("Cancel");
        gbc = new GridBagConstraints();
        gbc.gridx = 1;
        gbc.gridy = 0;
        gbc.weightx = 1.0;
        gbc.weighty = 1.0;
        gbc.fill = GridBagConstraints.HORIZONTAL;
        panel1.add(cancelButton, gbc);
        OKButton = new JButton();
        OKButton.setForeground(new Color(-13421773));
        OKButton.setText("OK");
        gbc = new GridBagConstraints();
        gbc.gridx = 0;
        gbc.gridy = 0;
        gbc.weightx = 1.0;
        gbc.weighty = 1.0;
        gbc.fill = GridBagConstraints.HORIZONTAL;
        panel1.add(OKButton, gbc);
        final JPanel panel2 = new JPanel();
        panel2.setLayout(new GridBagLayout());
        panel2.setMaximumSize(new Dimension(200, 2147483647));
        panel2.setMinimumSize(new Dimension(200, 200));
        panel2.setPreferredSize(new Dimension(500, 400));
        gbc = new GridBagConstraints();
        gbc.gridx = 0;
        gbc.gridy = 0;
        gbc.weightx = 1.0;
        gbc.weighty = 1.0;
        gbc.fill = GridBagConstraints.BOTH;
        browser.add(panel2, gbc);
        panel2.setBorder(BorderFactory.createTitledBorder(BorderFactory.createLineBorder(new Color(-13421773)), "Classes", TitledBorder.LEFT, TitledBorder.DEFAULT_POSITION, null, new Color(-6710887)));
        classes = new JList();
        classes.setMaximumSize(new Dimension(500, 20000));
        classes.setMinimumSize(new Dimension(200, 200));
        classes.setPreferredSize(new Dimension(500, 400));
        classes.setSelectionMode(0);
        gbc = new GridBagConstraints();
        gbc.gridx = 0;
        gbc.gridy = 0;
        gbc.weightx = 1.0;
        gbc.weighty = 1.0;
        gbc.fill = GridBagConstraints.BOTH;
        panel2.add(classes, gbc);
        final JPanel panel3 = new JPanel();
        panel3.setLayout(new GridBagLayout());
        panel3.setMaximumSize(new Dimension(200, 2147483647));
        panel3.setMinimumSize(new Dimension(200, 200));
        panel3.setPreferredSize(new Dimension(200, 400));
        gbc = new GridBagConstraints();
        gbc.gridx = 1;
        gbc.gridy = 0;
        gbc.weightx = 1.0;
        gbc.weighty = 1.0;
        gbc.fill = GridBagConstraints.BOTH;
        browser.add(panel3, gbc);
        panel3.setBorder(BorderFactory.createTitledBorder(BorderFactory.createLineBorder(new Color(-13421773)), "Methods", TitledBorder.DEFAULT_JUSTIFICATION, TitledBorder.DEFAULT_POSITION, null, new Color(-6710887)));
        methods = new JList();
        methods.setMaximumSize(new Dimension(200, 20000));
        methods.setMinimumSize(new Dimension(200, 200));
        methods.setPreferredSize(new Dimension(400, 500));
        methods.setSelectionMode(0);
        gbc = new GridBagConstraints();
        gbc.gridx = 0;
        gbc.gridy = 0;
        gbc.weightx = 1.0;
        gbc.weighty = 1.0;
        gbc.fill = GridBagConstraints.BOTH;
        panel3.add(methods, gbc);
        final JPanel panel4 = new JPanel();
        panel4.setLayout(new GridBagLayout());
        panel4.setMaximumSize(new Dimension(200, 2147483647));
        panel4.setMinimumSize(new Dimension(200, 26));
        panel4.setPreferredSize(new Dimension(200, 400));
        gbc = new GridBagConstraints();
        gbc.gridx = 2;
        gbc.gridy = 0;
        gbc.weightx = 1.0;
        gbc.weighty = 1.0;
        gbc.fill = GridBagConstraints.BOTH;
        browser.add(panel4, gbc);
        panel4.setBorder(BorderFactory.createTitledBorder(BorderFactory.createLineBorder(new Color(-13421773)), "Proofobligations", TitledBorder.DEFAULT_JUSTIFICATION, TitledBorder.DEFAULT_POSITION, null, new Color(-6710887)));
        proofObligation = new JList();
        proofObligation.setMaximumSize(new Dimension(200, 20000));
        proofObligation.setMinimumSize(new Dimension(200, 200));
        proofObligation.setPreferredSize(new Dimension(200, 200));
        proofObligation.setSelectionMode(0);
        gbc = new GridBagConstraints();
        gbc.gridx = 0;
        gbc.gridy = 0;
        gbc.weightx = 1.0;
        gbc.weighty = 1.0;
        gbc.fill = GridBagConstraints.BOTH;
        panel4.add(proofObligation, gbc);
    }

    /**
     * @noinspection ALL
     */
    public JComponent $$$getRootComponent$$$() {
        return browser;
    }
}
