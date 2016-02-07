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
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;

/**
 * 
 * Copied from TacletMenu and adapted to JavaFX style.
 * This is NOT a menu anymore but a controller. There is a field
 * rootMenu to access the actual menu.
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
    
    @FXML
    private ContextMenu rootMenu;
    @FXML
    private MenuItem noRules;
    @FXML 
    private Menu moreRules;
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
    
    
    public void init(ImmutableList<TacletApp> findList, ImmutableList<TacletApp> rewriteList,
            ImmutableList<TacletApp> noFindList, ImmutableList<BuiltInRule> builtInList, PosInSequent pos) {
        this.pos = pos;
        comp = new TacletAppComparator();
        createTacletMenu(removeRewrites(findList).prepend(rewriteList),
                noFindList, builtInList);
        proofMacroMenuController.init(mediator, pos.getPosInOccurrence());
    }
    
    /** removes RewriteTaclet from list
     * @param list the IList<Taclet> from where the RewriteTaclet are
     * removed
     * @return list without RewriteTaclets
     */
    private static ImmutableList<TacletApp> removeRewrites(ImmutableList<TacletApp> list) {
        ImmutableList<TacletApp> result = ImmutableSLList.<TacletApp>nil();
        Iterator<TacletApp> it = list.iterator();
    
        while(it.hasNext()) {
            TacletApp tacletApp = it.next();
            Taclet taclet=tacletApp.taclet();
            result = (taclet instanceof RewriteTaclet ? result :
                  result.prepend(tacletApp));
        }
        return result;
    }

    /** creates the menu by adding all sub-menus and items */
    private void createTacletMenu(ImmutableList<TacletApp> find,
                  ImmutableList<TacletApp> noFind,
                  ImmutableList<BuiltInRule> builtInList) {


        ImmutableList<TacletApp> toAdd = sort(find, comp);
        boolean rulesAvailable =  find.size() > 0;

        if (pos != null && pos.isSequent()) {
            rulesAvailable |= noFind.size() > 0;
            toAdd = toAdd.prepend(noFind);
        }
        
        if (rulesAvailable) {
            createMenuItems(toAdd);
        } else {
            noRules.setVisible(true);
        }
    }
    
    private void createMenuItems(ImmutableList<TacletApp> taclets){
        
        /*
         * final InsertHiddenTacletMenuItem insHiddenItem =
            new InsertHiddenTacletMenuItem(MainWindow.getInstance(),
                    mediator.getNotationInfo(), mediator.getServices());

        final InsertionTacletBrowserMenuItem insSystemInvItem =
            new InsertSystemInvariantTacletMenuItem(MainWindow.getInstance(),
                    mediator.getNotationInfo(), mediator.getServices());


        for (final TacletApp app : taclets) {
            final Taclet taclet = app.taclet();

            if (insHiddenItem.isResponsible(taclet)) {
                insHiddenItem.add(app);
            } else if (insSystemInvItem.isResponsible(taclet)) {
                insSystemInvItem.add(app);
            }
    }

        if (insHiddenItem.getAppSize() > 0) {
            add(insHiddenItem);
            insHiddenItem.addActionListener(control);
        }

        if (insSystemInvItem.getAppSize() > 0) {
            add(insSystemInvItem);
            insSystemInvItem.addActionListener(control);
        }

         */
        int idx = 0;
        for (final TacletApp app : taclets) {
            final Taclet taclet = app.taclet();
            
            if(!mediator.getFilterForInteractiveProving().filter(taclet)){
                continue;
            }

            //if (! insHiddenItem.isResponsible(taclet) &&
            //    !insSystemInvItem.isResponsible(taclet)) {
                
                final MenuItem item = new MenuItem(taclet.displayName());
                item.setOnAction(event -> {
                    Goal goal = mediator.getSelectedGoal();
                    mediator.getUI().getProofControl().selectedTaclet(taclet, goal, pos.getPosInOccurrence());
                });
                
                boolean rareRule = false;
                for (RuleSet rs : taclet.getRuleSets()) {
                    if (CLUTTER_RULESETS.contains(rs.name())) rareRule = true;
                }
                if (CLUTTER_RULES.contains(taclet.name())) rareRule = true;

                if (rareRule)
                    moreRules.getItems().add(item);
                else rootMenu.getItems().add(idx++,item);
            //}
        }
        if (moreRules.getItems().size() > 0)
            moreRules.setVisible(true);
    }
    
    
    
    public static ImmutableList<TacletApp> sort(ImmutableList<TacletApp> finds, TacletAppComparator comp) {
        ImmutableList<TacletApp> result = ImmutableSLList.<TacletApp>nil();
    
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
    };

    @FXML
    private void handleFocussedRuleApplication(ActionEvent event) {
        mediator.getUI().getProofControl().startFocussedAutoMode(
                pos.getPosInOccurrence(), mediator.getSelectedGoal());
    }
    
    @FXML 
    private void handleCopyToClipboard(ActionEvent event) {
        //TODO implement
    }
    
    @FXML 
    private void handleCreateAbbriviation(ActionEvent event) {
        //TODO implement
    }
    
    @FXML 
    private void handleEnableAbbriviation(ActionEvent event) {
        //TODO implement
    }
    
    @FXML 
    private void handleDisableAbbriviation(ActionEvent event) {
        //TODO implement
    }
    
    @FXML 
    private void handleChangeAbbriviation(ActionEvent event) {
        //TODO implement
    }
    
}
