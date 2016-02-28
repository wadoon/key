package de.uka.ilkd.key.nui.view.menu;

import java.net.URL;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.ResourceBundle;
import java.util.Set;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.nodeviews.TacletMenu.TacletAppComparator;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.view.SequentViewController;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.ui.MediatorProofControl;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;
import javafx.scene.input.Clipboard;
import javafx.scene.input.ClipboardContent;

/**
 * 
 * Copied from TacletMenu and adapted to JavaFX style. This is NOT a menu
 * anymore but a controller. There is a field rootMenu to access the actual
 * menu.
 * 
 * @see de.uka.ilkd.key.gui.nodeviews.TacletMenu original TacletMenu
 * @author Victor Schuemmer
 */
public class TacletMenuController extends ViewController {

    private static final Set<Name> CLUTTER_RULESETS = new LinkedHashSet<Name>();

    static {
        CLUTTER_RULESETS.add(new Name("notHumanReadable"));
        CLUTTER_RULESETS.add(new Name("obsolete"));
        CLUTTER_RULESETS.add(new Name("pullOutQuantifierAll"));
        CLUTTER_RULESETS.add(new Name("pullOutQuantifierEx"));
    }

    private static final Set<Name> CLUTTER_RULES = new LinkedHashSet<Name>();

    static {
        CLUTTER_RULES.add(new Name("cut_direct_r"));
        CLUTTER_RULES.add(new Name("cut_direct_l"));
        CLUTTER_RULES.add(new Name("case_distinction_r"));
        CLUTTER_RULES.add(new Name("case_distinction_l"));
        CLUTTER_RULES.add(new Name("local_cut"));
        CLUTTER_RULES.add(new Name("commute_and_2"));
        CLUTTER_RULES.add(new Name("commute_or_2"));
        CLUTTER_RULES.add(new Name("boxToDiamond"));
        CLUTTER_RULES.add(new Name("pullOut"));
        CLUTTER_RULES.add(new Name("typeStatic"));
        CLUTTER_RULES.add(new Name("less_is_total"));
        CLUTTER_RULES.add(new Name("less_zero_is_total"));
        CLUTTER_RULES.add(new Name("applyEqReverse"));

        // the following are used for drag'n'drop interactions
        CLUTTER_RULES.add(new Name("eqTermCut"));
        CLUTTER_RULES.add(new Name("instAll"));
        CLUTTER_RULES.add(new Name("instEx"));
    }

    private PosInSequent pos;
    private KeYMediator mediator;
    private TacletAppComparator comp;
    private SequentViewController parentController;

    @FXML
    private ContextMenu rootMenu;
    @FXML
    private MenuItem noRules;
    @FXML
    private Menu moreRules;
    @FXML
    private Menu insertHidden;
    @FXML
    private InsertHiddenMenuController insertHiddenController;
    @FXML
    private MenuItem copyToClipboard;
    @FXML
    private MenuItem createAbbr;
    @FXML
    private MenuItem enableAbbr;
    @FXML
    private MenuItem disableAbbr;
    @FXML
    private MenuItem changeAbbr;
    @FXML
    private ProofMacroMenuController proofMacroMenuController;

    public void init(PosInSequent pos, ViewController parentController) {
        this.pos = pos;
        this.parentController = (SequentViewController) parentController;

        if (pos != null) {
            MediatorProofControl c = mediator.getUI().getProofControl();
            Goal goal = mediator.getSelectedGoal();
            PosInOccurrence occ = pos.getPosInOccurrence();

            final ImmutableList<BuiltInRule> builtInRules = c
                    .getBuiltInRule(goal, occ);
            createTacletMenu(
                    removeRewrites(c.getFindTaclet(goal, occ))
                            .prepend(c.getRewriteTaclet(goal, occ)),
                    c.getNoFindTaclet(goal), builtInRules);
            proofMacroMenuController.init(mediator, pos.getPosInOccurrence());
        }
    }

    /**
     * removes RewriteTaclet from list
     * 
     * @param list
     *            the IList<Taclet> from where the RewriteTaclet are removed
     * @return list without RewriteTaclets
     */
    private static ImmutableList<TacletApp> removeRewrites(
            ImmutableList<TacletApp> list) {
        ImmutableList<TacletApp> result = ImmutableSLList.<TacletApp> nil();
        Iterator<TacletApp> it = list.iterator();

        while (it.hasNext()) {
            TacletApp tacletApp = it.next();
            Taclet taclet = tacletApp.taclet();
            result = (taclet instanceof RewriteTaclet ? result
                    : result.prepend(tacletApp));
        }
        return result;
    }

    /** creates the menu by adding all sub-menus and items */
    private void createTacletMenu(ImmutableList<TacletApp> find,
            ImmutableList<TacletApp> noFind,
            ImmutableList<BuiltInRule> builtInList) {

        ImmutableList<TacletApp> toAdd = sort(find, comp);
        boolean rulesAvailable = find.size() > 0;

        if (pos != null && pos.isSequent()) {
            rulesAvailable |= noFind.size() > 0;
            toAdd = toAdd.prepend(noFind);
        }

        if (rulesAvailable) {
            createMenuItems(toAdd);
        }
        else {
            noRules.setVisible(true);
        }
    }

    private void createMenuItems(ImmutableList<TacletApp> taclets) {
        int idx = 0;
        for (final TacletApp app : taclets) {
            final Taclet taclet = app.taclet();

            if (!mediator.getFilterForInteractiveProving().filter(taclet)) {
                continue;
            }

            final TacletMenuItem item = new TacletMenuItem(app,
                    mediator.getNotationInfo(), mediator.getServices());
            item.setOnAction(this::handleRuleApplication);

            if (insertHiddenController.isResponsible(item)) {
                insertHiddenController.add(item);
            }
            else {
                boolean rareRule = false;
                for (RuleSet rs : taclet.getRuleSets()) {
                    if (CLUTTER_RULESETS.contains(rs.name()))
                        rareRule = true;
                }
                if (CLUTTER_RULES.contains(taclet.name()))
                    rareRule = true;

                if (rareRule)
                    moreRules.getItems().add(item);
                else
                    rootMenu.getItems().add(idx++, item);
            }
        }
        if (moreRules.getItems().size() > 0)
            moreRules.setVisible(true);
        if (!insertHiddenController.isEmpty())
            insertHiddenController.setVisible(true);

    }

    public static ImmutableList<TacletApp> sort(ImmutableList<TacletApp> finds,
            TacletAppComparator comp) {
        ImmutableList<TacletApp> result = ImmutableSLList.<TacletApp> nil();

        List<TacletApp> list = new ArrayList<TacletApp>(finds.size());

        for (final TacletApp app : finds) {
            list.add(app);
        }

        Collections.sort(list, comp);

        for (final TacletApp app : list) {
            result = result.prepend(app);
        }

        return result;
    }

    @Override
    public void initialize(URL arg0, ResourceBundle arg1) {

    }

    @Override
    public void initializeAfterLoadingFxml() {
        mediator = getContext().getKeYMediator();
        comp = new TacletAppComparator();
        insertHiddenController.setMainApp(getMainApp(), getContext());
    };

    public void handleRuleApplication(ActionEvent event) {
        Goal goal = mediator.getSelectedGoal();
        mediator.getUI().getProofControl().selectedTaclet(
                ((TacletMenuItem) event.getSource()).getTaclet(), goal,
                pos.getPosInOccurrence());
    }

    @FXML
    private void handleFocussedRuleApplication(ActionEvent event) {
        mediator.getUI().getProofControl().startFocussedAutoMode(
                pos.getPosInOccurrence(), mediator.getSelectedGoal());
    }

    @FXML
    private void handleCopyToClipboard(ActionEvent event) {
        final Clipboard clipboard = Clipboard.getSystemClipboard();
        final ClipboardContent content = new ClipboardContent();
        content.putString(parentController.getProofString()
                .substring(pos.getBounds().start(), pos.getBounds().end()));
        clipboard.setContent(content);
    }

    @FXML
    private void handleCreateAbbriviation(ActionEvent event) {
        // TODO implement
    }

    @FXML
    private void handleEnableAbbriviation(ActionEvent event) {
        // TODO implement
    }

    @FXML
    private void handleDisableAbbriviation(ActionEvent event) {
        // TODO implement
    }

    @FXML
    private void handleChangeAbbriviation(ActionEvent event) {
        // TODO implement
    }

}
