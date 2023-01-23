package org.key_project.cache;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension.Info;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension.Startup;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension.Toolbar;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

/**
 * Entry point for the Proof Exploration Extension.
 *
 * @author Alexander Weigl
 * @version 1 (16.04.19)
 */
@Info(name = "Proof Caching",
    description = "This extension allows you to cache sequents which are known " +
        "to be provable to speed up reconduction of proof after small changes. " +
        "Proof nodes " +
        "Author: Mattias Ulbrich <ulbrich@kit.edu>",
    experimental = false, optional = true, priority = 10000)
public class CacheExtension implements KeYGuiExtension, Toolbar, Startup {
    private JToolBar toolBar;
    private Set<Hash> theCache = new HashSet<>();
    private boolean enabled;
    private ToggleProofCacheAction toggleAction;
    private KeYMediator mediator;

    public boolean isEnabled() {
        return enabled;
    }

    public void setEnabled(boolean enabled) {
        if (digest == null) {
            this.enabled = false;
        } else {
            this.enabled = enabled;
        }
        if (toggleAction != null) {
            toggleAction.putValue(Action.SELECTED_KEY, this.enabled);
        }
    }

    public void clearCache() {
        theCache.clear();
    }

    public void recordIntoCache() {
        if (theCache == null) {
            return;
        }

        Deque<Node> nodes = new LinkedList<>();
        nodes.add(mediator.getSelectedProof().root());
        while (!nodes.isEmpty()) {
            Node node = nodes.removeFirst();
            if (node.isClosed()) {
                theCache.add(getHash(node.sequent()));
            }
            Iterator<Node> it = node.childrenIterator();
            while (it.hasNext()) {
                nodes.add(it.next());
            }
        }
    }

    private static final class Hash {

        private final String print;

        public Hash(String string) {
            this.print = string;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o)
                return true;
            if (o == null || getClass() != o.getClass())
                return false;
            Hash hash = (Hash) o;
            return print.equals(hash.print);
        }

        @Override
        public int hashCode() {
            return print.hashCode();
        }

        @Override
        public String toString() {
            return print;
        }
    }

    private final MessageDigest digest;

    public CacheExtension() {
        MessageDigest dig;
        try {
            dig = MessageDigest.getInstance("SHA-256");
        } catch (NoSuchAlgorithmException e) {
            e.printStackTrace();
            dig = null;
        }
        this.digest = dig;
    }

    private final KeYSelectionListener selectionListener = new KeYSelectionListener() {
        private final Set<Proof> installedProofs =
            Collections.newSetFromMap(new IdentityHashMap<>());

        @Override
        public void selectedNodeChanged(KeYSelectionEvent e) {
            // nothing to do
        }

        @Override
        public void selectedProofChanged(KeYSelectionEvent e) {
            Proof proof = e.getSource().getSelectedProof();
            if (!installedProofs.contains(proof) && proof != null) {
                proof.addRuleAppListener(CacheExtension.this::ruleApplied);
                installedProofs.add(proof);
            }
        }
    };

    private void ruleApplied(ProofEvent proofEvent) {
        for (Goal newGoal : proofEvent.getNewGoals()) {
            Hash hash = getHash(newGoal.sequent());
            if (theCache.contains(hash) && isEnabled()) {
                newGoal.setEnabled(false);
            }
        }
    }

    private Hash getHash(Sequent sequent) {
        return new Hash(sequent.toString());
    }

    @Nonnull
    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        if (toolBar == null) {
            toolBar = new JToolBar();
            toolBar.add(new JLabel("Caching closed nodes: ",
                IconUtil.makeIcon(FontAwesomeSolid.DATABASE), JLabel.LEADING));
            toggleAction = new ToggleProofCacheAction(this);
            toolBar.add(new JToggleButton(toggleAction));
            toolBar.add(new JButton(new EmptyProofCachesAction(this)));
            toolBar.add(new JButton(new RecordCacheAction(this)));
        }
        return toolBar;
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        this.mediator = mediator;
        mediator.addKeYSelectionListener(selectionListener);
    }

}

