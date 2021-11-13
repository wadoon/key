package de.uka.ilkd.key.gui.extensions.fastcut;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.DefaultContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.nodeviews.CurrentGoalViewMenu;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.TermInstantiation;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.util.parsing.BuildingException;
import de.uka.ilkd.key.util.parsing.SyntaxErrorReporter;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (11/13/21)
 */
@KeYGuiExtension.Info(name = "Explorative Sideproof Rules",
        optional = true,
        experimental = false,
        description = "Allows to do stuff...",
        priority = 10000)
public class FastCut implements KeYGuiExtension, KeYGuiExtension.ContextMenu {
    private static final Name CUT_TACLET_NAME = new Name("cut");

    public static final File cutFile = getFastCutFile();

    /**
     * Environment variable or java system property where the cuts definition can be found.
     */
    public static final String FAST_CUT_FILE = "FAST_CUT_FILE";

    @Nonnull
    private static File getFastCutFile() {
        File file = new File(PathConfig.getKeyConfigDir(), "fastcuts.txt");
        if (System.getProperty(FAST_CUT_FILE) != null) {
            file = new File(System.getProperty(FAST_CUT_FILE));
        }
        if (System.getenv(FAST_CUT_FILE) != null) {
            file = new File(System.getProperty(FAST_CUT_FILE));
        }
        return file;
    }

    public final List<String> cutSnippets = new ArrayList<>();

    public FastCut() {
        try {
            if (cutFile.exists()) {
                var snippets =
                        Files.readAllLines(cutFile.toPath())
                                .stream().filter(it -> !it.startsWith("#"))
                                .collect(Collectors.toList());
                cutSnippets.addAll(snippets);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    @Nonnull
    @Override
    public List<Action> getContextActions(@Nonnull KeYMediator mediator,
                                          @Nonnull ContextMenuKind kind,
                                          @Nonnull Object underlyingObject) {
        if (kind == DefaultContextMenuKind.GOAL_VIEW) {
            var kio = new KeyIO(mediator.getSelectedProof().getServices());
            var seq = new ArrayList<Action>(cutSnippets.size() + 1);
            for (String it : cutSnippets) {
                if (it.startsWith("#") || it.isBlank()) continue;
                Term term;
                try {
                    term = kio.parseExpression(it);
                } catch (SyntaxErrorReporter.ParserException | BuildingException e) {
                    term = null;
                }
                var action = new ApplyFastCutAction(it, term, mediator,
                        (CurrentGoalViewMenu.GoalViewData) underlyingObject);
                seq.add(action);

            }
            seq.add(new GatherCutsAndStoreAction(mediator.getSelectedProof()));
            return seq;
        }
        return Collections.emptyList();
    }

    public class ApplyFastCutAction extends KeyAction {
        private final Proof proof;
        private final Term term;
        private final Goal goal;

        public ApplyFastCutAction(String line,
                                  Term term, KeYMediator mediator,
                                  CurrentGoalViewMenu.GoalViewData underlyingObject) {
            super();
            setMenuPath("Fast Cuts");
            setName(line);
            this.term = term;
            proof = mediator.getSelectedProof();
            goal = mediator.getSelectedGoal();

            setEnabled(term != null && goal != null);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            Taclet cut = proof.getEnv().getInitConfigForEnvironment()
                    .lookupActiveTaclet(CUT_TACLET_NAME);
            TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
            SchemaVariable cutFormula = app.uninstantiatedVars().iterator().next();
            app = app.addCheckedInstantiation(cutFormula, term, proof.getServices(), true);
            goal.apply(app);
        }
    }

    public class GatherCutsAndStoreAction extends KeyAction {
        private final Proof proof;

        public GatherCutsAndStoreAction(Proof proof) {
            super();
            setName("Gather cut terms and store them");
            setMenuPath("Fast Cuts");
            this.proof = proof;
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            try {
                var gathered = gatherCuts();
                cutSnippets.addAll(gathered);
                Files.createFile(cutFile.toPath());
                Files.write(cutFile.toPath(), cutSnippets);
            } catch (IOException ex) {
                ExceptionDialog.showDialog(MainWindow.getInstance(), ex);
            }
        }

        private List<String> gatherCuts() {
            final var iter = proof.root().subtreeIterator();
            var terms = new LinkedList<String>();
            while (iter != null && iter.hasNext()) {
                var n = iter.next();
                final var app = n.getAppliedRuleApp();
                if (app == null) continue;
                final var rule = app.rule();
                if (rule.name().equals(CUT_TACLET_NAME)) {
                    var tapp = (NoPosTacletApp) n.getAppliedRuleApp();
                    TermInstantiation instantiation = (TermInstantiation)
                            tapp.matchConditions().getInstantiations()
                                    .lookupEntryForSV(new Name("cutFormula")).value();
                    var cutFormula = instantiation.getInstantiation();
                    var repr = LogicPrinter.quickPrintTerm(cutFormula, proof.getServices());
                    System.out.println("cutFormula found: " + repr);
                    terms.add(repr);
                }
            }
            return terms;
        }
    }
}
