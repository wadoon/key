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

package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.util.Optional;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;

public final class LazySEPostProcLoopByInvariantAction
        extends MainWindowAction {
    private static final long serialVersionUID = 915588190956945751L;

    public LazySEPostProcLoopByInvariantAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Complete by Invariant Reasoning");
        setTooltip("Complete Lazy SE Loop Rule App by Invariant Reasoning");

        getMediator().enableWhenProofLoaded(this);
        getMediator().addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                if (!getMediator().ensureProofLoaded()) {
                    return;
                }

                final Proof loadedProof = getMediator().getSelectedProof();
                final boolean lazySEProofOptionSet = Optional
                        .ofNullable(
                            loadedProof.getSettings().getChoiceSettings()
                                    .getDefaultChoices().get("lazySymbExec"))
                        .orElse("").equals("lazySymbExec:on");
                //@formatter:off
//                final Iterable<Node> nodes = () -> loadedProof.root()
//                        .subtreeIterator();
//                final List<String> lazySEProofRules = //
//                        !lazySEProofOptionSet ? Collections.emptyList()
//                                : StreamSupport
//                                        .stream(nodes.spliterator(), false)
//                                        .map(Node::getAppliedRuleApp)
//                                        .filter(ra -> ra != null)
//                                        .map(RuleApp::rule).map(Rule::name)
//                                        .map(Name::toString)
//                                        .filter(
//                                            LazySEPostProcLoopByInvariantAction::isLazySERuleName)
//                                        .collect(Collectors.toList());
                //@formatter:on

                LazySEPostProcLoopByInvariantAction.this
                        .setEnabled(lazySEProofOptionSet);
            }
        });

    }

    //@formatter:off
//    /**
//     * Checks whether a given {@link Rule} name is a "lazy SE rule".
//     *
//     * TODO (DS, 2018-11-15): That's not the right place here, refactor it.
//     *
//     * @param ruleName
//     *            The rule name to check
//     * @return true iff the given {@link Rule} name is in a hard-coded array of
//     *         lazy SE rule names.
//     */
//    private static boolean isLazySERuleName(String ruleName) {
//        final String[] lazySERuleNames = new String[] { "lazyLoop" };
//        return Arrays.stream(lazySERuleNames)
//                .anyMatch(name -> name.equals(ruleName));
//    }
    //@formatter:on

    @Override
    public synchronized void actionPerformed(ActionEvent e) {
        // TODO
    }

}
