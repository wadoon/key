package de.uka.ilkd.key.kexext.backgroundSMT;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.prooftree.GUIAbstractTreeNode;
import de.uka.ilkd.key.gui.smt.ProgressDialog;
import de.uka.ilkd.key.gui.smt.SolverListener;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.smt.*;

import java.awt.event.ActionEvent;
import java.util.*;

public class ApplyBackgroundSolverAction extends KeyAction {

    private BackgroundSolverRunner runner;

    private Set<BackgroundSolverRunner> runners = new HashSet<>();
    private Map<BackgroundSolverRunner, Boolean> runnerStatus = new HashMap<>();

    private final Node treeNode;

    private final BackgroundSMTExtension extension;

    public ApplyBackgroundSolverAction(Node obj, BackgroundSMTExtension extension) {
        this.extension = extension;
        this.treeNode = obj;
    }

    @Override
    public void actionPerformed(ActionEvent actionEvent) {
        extension.applyRunner(treeNode);
    }

}
