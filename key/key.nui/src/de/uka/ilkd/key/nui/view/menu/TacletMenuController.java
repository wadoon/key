package de.uka.ilkd.key.nui.view.menu;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.nodeviews.TacletMenu;
import de.uka.ilkd.key.gui.nodeviews.TacletMenu.TacletAppComparator;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.view.SequentViewController;
import de.uka.ilkd.key.pp.AbbrevMap;
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
import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.TextInputDialog;
import javafx.scene.input.Clipboard;
import javafx.scene.input.ClipboardContent;

/**
 * 
 * Copied from TacletMenu and adapted to JavaFX style. This is NOT a menu
 * anymore but a view controller. There is a field rootMenu to access the actual
 * menu.
 * 
 * @see TacletMenu
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
    private Goal goal;
    private PosInOccurrence occ;

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
    public void initializeAfterLoadingFxml() {
        mediator = getContext().getKeYMediator();
        goal = mediator.getSelectedGoal();
        comp = new TacletAppComparator();
        insertHiddenController.setMainApp(getMainApp(), getContext());
    };

    /**
     * Use this method to pass additional Information that would normally given
     * to the constructor.
     * 
     * @param pos
     *            the position in the sequent for which the rules will be
     *            applied
     * @param parentController
     *            the SequentViewController that requested the menu
     * @throws IllegalArgumentException
     *             when pos is null
     */
    public void init(PosInSequent pos, ViewController parentController)
            throws IllegalArgumentException {
        if (pos == null)
            throw new IllegalArgumentException(
                    "Argument pos must not be null.");
        this.pos = pos;

        if (parentController instanceof SequentViewController) {
            this.parentController = (SequentViewController) parentController;
        }

        occ = pos.getPosInOccurrence();

        MediatorProofControl c = mediator.getUI().getProofControl();

        final ImmutableList<BuiltInRule> builtInRules = c.getBuiltInRule(goal,
                occ);
        createTacletMenu(
                removeRewrites(c.getFindTaclet(goal, occ))
                        .prepend(c.getRewriteTaclet(goal, occ)),
                c.getNoFindTaclet(goal), builtInRules);

        proofMacroMenuController.init(mediator, occ);
    }

    /**
     * Removes RewriteTaclet from the list.
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

    /**
     * Creates the menu by adding all sub-menus and items.
     * 
     * @param find
     * @param noFind
     * @param builtInList
     */
    private void createTacletMenu(ImmutableList<TacletApp> find,
            ImmutableList<TacletApp> noFind,
            ImmutableList<BuiltInRule> builtInList) {

        ImmutableList<TacletApp> toAdd = sort(find, comp);
        boolean rulesAvailable = find.size() > 0;

        if (pos.isSequent()) {
            rulesAvailable |= noFind.size() > 0;
            toAdd = toAdd.prepend(noFind);
        }

        if (rulesAvailable) {
            createMenuItems(toAdd);
        }
        else {
            noRules.setVisible(true);
        }

        if (occ != null)
            createAbbrevSection(pos.getPosInOccurrence().subTerm());

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

    private void createAbbrevSection(Term t) {
        AbbrevMap scm = mediator.getNotationInfo().getAbbrevMap();
        if (scm.containsTerm(t)) {
            changeAbbr.setVisible(true);
            if (scm.isEnabled(t)) {
                disableAbbr.setVisible(true);
            }
            else {
                enableAbbr.setVisible(true);
            }
        }
        else {
            createAbbr.setVisible(true);
        }
    }

    public void handleRuleApplication(ActionEvent event) {
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

    private boolean validateAbbreviation(String s) {
        if (s == null || s.length() == 0)
            return false;
        for (int i = 0; i < s.length(); i++) {
            if (!((s.charAt(i) <= '9' && s.charAt(i) >= '0')
                    || (s.charAt(i) <= 'z' && s.charAt(i) >= 'a')
                    || (s.charAt(i) <= 'Z' && s.charAt(i) >= 'A')
                    || s.charAt(i) == '_'))
                return false;
        }
        return true;
    }

    @FXML
    private void handleCreateAbbreviation(ActionEvent event) {
        if (occ.posInTerm() != null) {
            final String oldTerm = occ.subTerm().toString();
            final String term = oldTerm.length() > 200
                    ? oldTerm.substring(0, 200) : oldTerm;
            abbreviationDialog("Create Abbreviation",
                    "Enter abbreviation for term: \n" + term + "\n", null, occ,
                    false);
        }
    }

    @FXML
    private void handleChangeAbbreviation(ActionEvent event) {
        if (occ.posInTerm() != null) {
            abbreviationDialog("Change Abbreviation",
                    "Enter abbreviation for term: \n"
                            + occ.subTerm().toString(),
                    mediator.getNotationInfo().getAbbrevMap()
                            .getAbbrev(occ.subTerm()).substring(1),
                    occ, true);
        }
    }

    private void abbreviationDialog(String header, String message,
            String inputText, PosInOccurrence occ, boolean change) {
        TextInputDialog dialog = new TextInputDialog(inputText);
        dialog.setHeaderText(header);
        dialog.setContentText(message);
        Optional<String> result = dialog.showAndWait();
        result.ifPresent(abbreviation -> {
            if (abbreviation != null) {
                if (!validateAbbreviation(abbreviation)) {
                    getMainApp().showAlert("Sorry", null,
                            "Only letters, numbers and '_' are allowed for Abbreviations",
                            AlertType.INFORMATION);
                }
                else {
                    try {
                        if (change)
                            mediator.getNotationInfo().getAbbrevMap()
                                    .changeAbbrev(occ.subTerm(), abbreviation);
                        else
                            mediator.getNotationInfo().getAbbrevMap()
                                    .put(occ.subTerm(), abbreviation, true);
                        parentController.forceRefresh();
                    }
                    catch (Exception e) {
                        getMainApp().showAlert("Sorry",
                                "Something has gone wrong.", e.getMessage(),
                                AlertType.ERROR);
                    }
                }
            }
        });
    }

    @FXML
    private void handleEnableAbbreviation(ActionEvent event) {
        if (occ.posInTerm() != null) {
            mediator.getNotationInfo().getAbbrevMap().setEnabled(occ.subTerm(),
                    true);
            parentController.forceRefresh();
        }
    }

    @FXML
    private void handleDisableAbbreviation(ActionEvent event) {
        if (occ.posInTerm() != null) {
            mediator.getNotationInfo().getAbbrevMap().setEnabled(occ.subTerm(),
                    false);
            parentController.forceRefresh();
        }
    }

}
