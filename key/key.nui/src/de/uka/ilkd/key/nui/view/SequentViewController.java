package de.uka.ilkd.key.nui.view;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.nui.MainApp;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.proof.GoalChooserBuilder;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.RuleCollection;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.util.pp.Layouter;
import javafx.fxml.FXML;

public class SequentViewController {
    
    private Layouter layouter;
    private Sequent seq;
    private LogicPrinter lp = new LogicPrinter(new ProgramPrinter(), new NotationInfo(), null, true);
    private SequentViewLogicPrinter sqvlp;
    private Semisequent ssa;
    private Semisequent ssb;
    private ImmutableList<SequentFormula> ListA;
    private ImmutableList<SequentFormula> ListB;
    private Term t1;
    private Term t2;
    private Proof proof = new Proof("testProof", new InitConfig(new Services(null)));
    private Services services = proof.getServices();
    private TermBuilder tb = new TermBuilder(new TermFactory(null), services);
    
    // Reference to the main application.
    private MainApp mainApp;
    
    
    /**
     * The constructor.
     * The constructor is called before the initialize() method.
     */
    public SequentViewController() {
    }

    /**
     * Initializes the controller class. This method is automatically called
     * after the fxml file has been loaded.
     */
    @FXML
    private void initialize() {
    }
    
    /**
     * Is called by the main application to give a reference back to itself.
     * 
     * @param mainApp
     */
    public void setMainApp(MainApp mainApp) {
        this.mainApp = mainApp;
    }
    
    @FXML
    private void printSomething() throws ParserException {
        
        t1 = tb.parseTerm("abc");
        //t2 = tb.parseTerm("def");
        //ListA.prepend(new SequentFormula(t1));
        //ListB.prepend(new SequentFormula(t2));
        
        //ssa.insertFirst(ListA);
        //ssb.insertFirst(ListB);
        
        //seq = Sequent.createSequent(ssa, ssb);
        
        //lp.printSequent(seq);
        //System.out.println(LogicPrinter.quickPrintSequent(seq, null));
    }
}
