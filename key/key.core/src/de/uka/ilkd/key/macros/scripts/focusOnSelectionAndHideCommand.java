package de.uka.ilkd.key.macros.scripts;

import com.sun.org.apache.xerces.internal.impl.xpath.regex.RegularExpression;
import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.recoderext.RegisteredEscapeExpression;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;

import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.proofevent.RuleAppInfo;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import java.util.*;

/**
 * Hide all formulas that are not selected
 *  Created by sarah on 1/12/17.
 */
public class focusOnSelectionAndHideCommand extends AbstractCommand {
    private Proof proof;
    private Map<String, String> args;
    private Map<String, Object> stateMap;
    private String[] termsToKeep;



    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Proof proof, Map<String, String> args,
                        Map<String, Object> stateMap) throws ScriptException, InterruptedException {

        this.proof = proof;
        this.stateMap = stateMap;
        this.args = args;

        String formulaString = args.get("formula");
        if(formulaString == null) {
            throw new ScriptException("Missing 'formula' argument for focus");
        }

        termsToKeep = parseFormulaList(formulaString);

        try {
            hideAll();
        } catch (ParserException e) {
            e.printStackTrace();
        }

    }

    @Override
    public String getName() {
        return "focus";
    }

    /**
     * Hide all formulas of teh seuqent that are not in the list tokeep
     * @throws ParserException
     * @throws ScriptException
     */
    private void hideAll() throws ParserException, ScriptException{
        while(true){
        Object fixedGoal = stateMap.get(GOAL_KEY);
        if(fixedGoal instanceof Node) {
            Node fixed = (Node) fixedGoal;
            //case node is already modfied by foucs, the child has to be returend
            if(!fixed.leaf()){
                assert fixed.childrenCount() == 1;
                fixed = fixed.child(0);
            }

            Goal g = getGoal(proof.openGoals(), fixed);

            SequentFormula toHide = null;
            if (g != null) {

                toHide = iterateThroughSequentAndFindNonMatch(g);
                //as long as there is a match
                if (toHide != null) {
                    boolean antec = false;

                        Taclet tac;
                        if (g.sequent().antecedent().contains(toHide)) {
                            tac = getTaclet(toHide.formula(), "left");
                            antec = true;

                        } else {
                            tac = getTaclet(toHide.formula(), "right");

                        }
                        makeTacletApp(g, toHide, tac, antec);

                } else {
                    //no formulas to hide any more on sequent
                    break;
                }

            }else{
                //no goal found
                break;
            }
        }


        }
    }

    /**
     * Replace \n, whitepaces and seperating characters and return list with string representation of formula to hide
     * This has to be adapted when syntax is clear
     */
    private String[] parseFormulaList(String formList){


        String[] forms = formList.split("],");
        String temp = "";
        for(int i = 0; i < forms.length; i++){
            temp = forms[i];
            temp = temp.replaceAll("\n", "");
            temp = temp.replaceAll(" ", "");
            temp = temp.trim();
            temp = temp.substring(1);
            if(temp.endsWith("]")){
                temp= temp.substring(0, temp.length()-1);
            }
            System.out.println(temp);
            forms[i] = temp;
        }

        return forms;
    }

    //determine where formula in sequent and apply either hide_left or hide_right
    private Taclet getTaclet(Term t, String pos) throws ScriptException{
        String ruleName;
        Taclet tac;
        switch(pos){
            case "left":
                ruleName = "hide_left";
                break;
            case "right":
                ruleName ="hide_right";
                break;
            default:
                ruleName ="";
                throw new ScriptException("Position of term "+t.toString()+ "unknown");
        }

        tac = proof.getEnv().getInitConfigForEnvironment().lookupActiveTaclet(new Name(ruleName));

        return tac;


    }

    /**
     * Iterate through sequent and find first formula that is not in the list of formulas to keep and return this formula
     * @param g
     * @return formula to hide, if all formulas in the sequent should be kept, returns null
     * @throws ScriptException
     * @throws ParserException
     */

    private SequentFormula iterateThroughSequentAndFindNonMatch(Goal g) throws ScriptException, ParserException {
        Sequent seq = g.sequent();
        Iterator<SequentFormula> iterator = seq.iterator();
        while(iterator.hasNext()){
            SequentFormula form = iterator.next();


            Boolean isIn = false;
            for(int i = 0; i< termsToKeep.length; i++){
                Term t = toTerm(proof, g, stateMap, termsToKeep[i], Sort.FORMULA);
                //String comparison for updates in formulas, as terms appear to not be equal
                if(form.formula().equals(t) || (form.formula().toString().equals(t.toString()))){
                    isIn = true;
                }
            }
            if(!isIn){
                return form;
            }
        }
        return null;
    }

    /**
     * Make tacletApp for one sequentformula to hide on the seuqent
     * @param g the goal on which this hide rule should be applied to
     * @param toHide the sequentformula to hide
     * @param tac the taclet top apply (either hide_left or hide_right)
     * @param antec whether teh formula is in the antecedent
     * @throws ScriptException
     */
    private void makeTacletApp(Goal g, SequentFormula toHide, Taclet tac, boolean antec) throws ScriptException{


       //hide rules only applicable to top-level terms/sequent formulas
        PosInTerm pit = PosInTerm.getTopLevel();

        PosInOccurrence pio = new PosInOccurrence(toHide, pit, antec);

        Set<SchemaVariable> svs = tac.collectSchemaVars();
        assert  svs.size() == 1;
        Iterator iter = svs.iterator();
        SchemaVariable sv = (SchemaVariable) iter.next();

        SVInstantiations inst = SVInstantiations.EMPTY_SVINSTANTIATIONS;

        TacletApp app = PosTacletApp.createPosTacletApp((FindTaclet) tac, inst , pio, proof.getServices());
        app = app.addCheckedInstantiation(sv, toHide.formula(), proof.getServices(), true);
        g.apply(app);



    }


}
/*
rule allRight;
rule impRight;
rule methodCall;
branches;
	simp-upd;
        rule methodBodyExpand;
	simp-upd;
	focus formula="[ {heap:=store(heap, p, Person::$age, x_0)}
  \<{method-frame(source=birthday()@Person,this=p): {
        if (this.age>=0) {
          this.age++;
        }
      }
    }\> gt(int::select(heap, p, Person::$age), x_0)]";
next;
        simp-upd;
	focus formula="[p = null]";
end;

rule allRight;
rule impRight;
rule methodCall;
branches;
        skip;
next;
        simp-upd;
	focus formula="[p = null]";
end;

, [geq(x_0, Z(0(#)))]



*/
