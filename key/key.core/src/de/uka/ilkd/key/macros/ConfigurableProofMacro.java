package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import org.key_project.util.collection.ImmutableList;

import javax.swing.*;
import javax.swing.table.AbstractTableModel;
import java.awt.*;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (30.05.18)
 */
public abstract class ConfigurableProofMacro<Macro extends ProofMacro> extends StrategyProofMacro {
    /**
     *
     */
    protected final Macro internal;

    protected AdaptableStrategy strategy;
    protected AdaptableStrategy.RuleNameAndSetAdapter costAdapter;

    public ConfigurableProofMacro(Macro internal) {
        this.internal = internal;
    }

    private static List<Taclet> findTaclets(Proof p) {
        Goal g = p.openGoals().head();
        Services services = p.getServices();
        TacletFilter filter = new TacletFilter() {
            @Override
            protected boolean filter(Taclet taclet) {
                return true;
            }
        };
        List<Taclet> set = new ArrayList<>();
        RuleAppIndex index = g.ruleAppIndex();
        index.tacletIndex().allNoPosTacletApps().forEach(t ->
                set.add(t.taclet())
        );

/*        index.autoModeStopped();
        for (SequentFormula sf : g.node().sequent().antecedent()) {
            ImmutableList<TacletApp> apps = index.getTacletAppAtAndBelow(filter,
                    new PosInOccurrence(sf, PosInTerm.getTopLevel(), true),
                    services);
            apps.forEach(t -> set.add(t.taclet()));
        }

        try {
            for (SequentFormula sf : g.node().sequent().succedent()) {
                ImmutableList<TacletApp> apps = index.getTacletAppAtAndBelow(filter,
                        new PosInOccurrence(sf, PosInTerm.getTopLevel(), true),
                        services);
                apps.forEach(t -> set.add(t.taclet()));
            }
        } catch (NullPointerException e) {
            e.printStackTrace();
        }
  */
        return set;
    }

    @Override
    protected AdaptableStrategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
        if (this.strategy == null) {
            this.strategy = new AdaptableStrategy(proof.getActiveStrategy());
            this.costAdapter = new AdaptableStrategy.RuleNameAndSetAdapter();
            this.strategy.costAdapter = this.costAdapter;
        }
        return this.strategy;
    }

    @Override
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc) {
        return internal.canApplyTo(proof, goals, posInOcc);
    }

    @Override
    public boolean canApplyTo(Node node, PosInOccurrence posInOcc) {
        return internal.canApplyTo(node, posInOcc);
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof,
                                          ImmutableList<Goal> goals, PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws InterruptedException {
        createStrategy(proof, null);
        updateStrategyDialog(proof);
        proof.setActiveStrategy(strategy);
        ProofMacroFinishedInfo info = null;
        try {
            info = internal.applyTo(uic, proof, goals, posInOcc, listener);
        } catch (Exception e) {
            e.printStackTrace();
        }
        proof.setActiveStrategy(strategy.delegate);
        return info;
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Node node, PosInOccurrence posInOcc,
                                          ProverTaskListener listener) throws Exception {
        updateStrategyDialog(node.proof());
        node.proof().setActiveStrategy(strategy);
        ProofMacroFinishedInfo info = internal.applyTo(uic, node, posInOcc, listener);
        node.proof().setActiveStrategy(strategy.delegate);
        return info;
    }

    private void updateStrategyDialog(Proof proof) {
        createStrategy(proof, null);

        JPanel panel = new JPanel(new BorderLayout());
        JTabbedPane tabbedPane = new JTabbedPane();

        List<Taclet> taclets = findTaclets(proof);
        List<String> tacletNames = findTaclets(proof).stream()
                .map(Taclet::name)
                .map(Object::toString)
                .sorted()
                .distinct()
                .collect(Collectors.toList());

        List<String> ruleSetNames = taclets.stream()
                .flatMap(t -> t.getRuleSets().stream())
                .map(RuleSet::name)
                .map(Object::toString)
                .sorted()
                .distinct()
                .collect(Collectors.toList());


        JTable tacletFactor = new JTable(new TacletCostModel(tacletNames, costAdapter.ruleName));
        tabbedPane.addTab("Taclet Factor", new JScrollPane(tacletFactor));


        JTable ruleSetFactor = new JTable(new TacletCostModel(ruleSetNames, costAdapter.ruleSet));
        tabbedPane.addTab("RuleSet Factor", new JScrollPane(ruleSetFactor));

        panel.add(tabbedPane);
        JDialog dialog = new JDialog((Dialog) null, "Change Strategy Settings (locally)", true);
        dialog.setContentPane(panel);
        dialog.setSize(300, 600);

        JPanel buttons = new JPanel(new FlowLayout(FlowLayout.CENTER));
        JButton btnOk = new JButton("Run");
        btnOk.addActionListener(evt -> {
            dialog.setVisible(false);
        });
        buttons.add(btnOk);
        panel.add(buttons, BorderLayout.SOUTH);
        dialog.setVisible(true);
    }


    private class TacletCostModel extends AbstractTableModel {
        private final AdaptableStrategy.SetBasedCostAdapter<String> costAdapter;
        private final List<String> keys;

        public TacletCostModel(List<String> keys, AdaptableStrategy.SetBasedCostAdapter<String> ruleSet) {
            this.keys = keys;
            costAdapter = ruleSet;
        }

        @Override
        public int getRowCount() {
            return keys.size();
        }

        @Override
        public int getColumnCount() {
            return 3;
        }

        @Override
        public String getColumnName(int columnIndex) {
            switch (columnIndex) {
                case 0:
                    return "Taclet";
                case 1:
                    return "Cost Factor";
                case 2:
                    return "Cost Summand";
                default:
                    return "";
            }
        }

        @Override
        public Class<?> getColumnClass(int columnIndex) {
            switch (columnIndex) {
                case 0:
                    return String.class;
                case 1:
                case 2:
                    return Integer.class;
                default:
                    return Object.class;
            }
        }

        @Override
        public boolean isCellEditable(int rowIndex, int columnIndex) {
            return columnIndex == 1 || columnIndex == 2;
        }

        @Override
        public Object getValueAt(int rowIndex, int columnIndex) {
            try {
                String name = keys.get(rowIndex);
                switch (columnIndex) {
                    case 0:
                        return name;
                    case 1:
                        return costAdapter.factorMap.getOrDefault(name, 1L);
                    case 2:
                        return costAdapter.summandMap.getOrDefault(name, 0L);
                }
            } catch (IndexOutOfBoundsException e) {
                e.printStackTrace();
            }
            return "";
        }

        @Override
        public void setValueAt(Object aValue, int rowIndex, int columnIndex) {
            String name = keys.get(rowIndex);
            long l = Long.parseLong(aValue.toString());
            if (columnIndex == 1) {
                costAdapter.factorMap.put(name, l);
            } else {
                costAdapter.summandMap.put(name, l);
            }
        }
    }

}

