package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.Varargs;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class UseContractCommand extends AbstractCommand<UseContractCommand.Parameters> {


    public static class Parameters {
        @Option(value = "type", required = true)
        public String contractType;
        @Option(value = "on", required = false)
        public Term on;
        @Option(value = "formula", required = false)
        public Term formula;
        @Option(value = "occ", required = false)
        public int occ = -1;
        @Option(value = "heapConfig", required = false)
        public Term heap;
        @Option(value = "contract", required = false)
        public String contract;

    }

    public UseContractCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "useContract";
    }

    @Override
    public Parameters evaluateArguments(EngineState state, Map<String, String> arguments) throws Exception {
        Parameters p = state.getValueInjector().inject(this, new Parameters(), arguments);

        if (!p.contractType.equals("dependency") && !p.contractType.equals("method")) {
            throw new ScriptException("The contract type " + p.contractType + "is currently not supported");
        }
        if (p.contractType.equals("dependency")) {
            if (p.on == null) {
                throw new ScriptException("Dependency Contracts need a term to where to apply them.");
            }
        }

        return p;
        //contract und heapConfig


    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Parameters args, EngineState stateMap) throws ScriptException, InterruptedException {
        Goal goal = stateMap.getFirstOpenGoal();

        String type = args.contractType;
        //TODO adjust if more than one type possible
        UseDependencyContractRule rule = UseDependencyContractRule.INSTANCE;
        ProofControl proofControl = uiControl.getProofControl();

        PosInOccurrence termPio = findTermPio(goal.sequent(), args.on, args.formula);

        if (termPio == null) {
            throw new ScriptException("For the rule useContract is more than one position to apply possible, " +
                    "please consider specifying the formula in which the term to apply appears");
        }


        //complete and apply the rule

        ImmutableSet<IBuiltInRuleApp> result = DefaultImmutableSet.<IBuiltInRuleApp>nil();

        for (final IBuiltInRuleApp app : goal.ruleAppIndex().
                getBuiltInRules(goal, termPio)) {
            if (app.rule() == rule) {
                result = result.add(app);
            }
        }
        //there should only be one dependency contract built in rule
        assert result.size() == 1;
        IBuiltInRuleApp app = result.iterator().next();

        if (!app.complete()) {
            app = complete(app, goal, args);
        }

        if(!app.complete()){
            throw new ScriptException("Could not complete Rule application for Dependency contract. Please consider specifying the heap context");
        }
        if (app != null && app.rule() == rule) {
            goal.apply(app);
            return;
        }




    }

    /**
     * Complete built in rule
     * @param app
     * @param goal
     * @return
     */
    private IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal, Parameters p) throws ScriptException {
        UseDependencyContractApp cApp = (UseDependencyContractApp) app;

        Services services = goal.proof().getServices();

        cApp = cApp.tryToInstantiateContract(services);
        final List<PosInOccurrence> steps = UseDependencyContractRule.getSteps(
                cApp.getHeapContext(),
                cApp.posInOccurrence(), goal.sequent(), services);
        if(p.heap == null) {

            if (steps.size() == 1) {
                return cApp.setStep(steps.get(0));
            } else {
                return null;
            }
        } else {
            if(steps.size() > 0){
                for (int i = 0; i < steps.size(); i++) {
                    PosInOccurrence posInOccurrence =  steps.get(i);
                    if(posInOccurrence.subTerm().equalsModRenaming(p.heap)){
                        return cApp.setStep(steps.get(i));
                    }
                }
                throw new ScriptException("Cannot find heapconfig "+p.heap+" in SequentFormula "+cApp.posInOccurrence());
            } else {
                throw new ScriptException("There is no heapconfig "+p.heap+" in SequentFormula "+cApp.posInOccurrence());
            }
            /*PosInOccurrence pio =
                    findTermInSeqFormula(cApp.posInOccurrence().sequentFormula(), p.heap, cApp.posInOccurrence().isInAntec());
            if(pio == null || !steps.contains(pio)){
                throw new ScriptException("Cannot find heapconfig "+p.heap+" in SequentFormula "+cApp.posInOccurrence());
            } else {
                for (int i = 0; i < steps.size(); i++) {
                    PosInOccurrence posInOccurrence =  steps.get(i);
                    if(posInOccurrence.eqEquals(pio)){
                        return cApp.setStep(steps.get(i));
                    }
                }
            }*/
        }
      //  return null;
    }


    /**
     * Find the position of the on term on the sequent.
     * It is possible but not necessary to specifiy the formula in which the on term is in.
     *
     * @param seq
     * @param on
     * @param formula
     * @return
     * @throws ScriptException
     */
    private PosInOccurrence findTermPio(Sequent seq, Term on, Term formula) throws ScriptException {
        PosInOccurrence tempPioAntec = null;
        PosInOccurrence tempPioSucc = null;
        PosInOccurrence pio = null;
        List<PosInOccurrence> foundPositionsAntec = new ArrayList<>();
        List<PosInOccurrence> foundPositionsSucc = new ArrayList<>();
        for (SequentFormula sf : seq.antecedent()) {
            if (formula != null && !sf.formula().equalsModRenaming(formula)) {
                continue;
            } else {
                tempPioAntec = findTermInSeqFormula(sf, on, true);
                if (tempPioAntec != null) {
                    foundPositionsAntec.add(tempPioAntec);
                }

            }
        }
        for (SequentFormula sf : seq.succedent()) {
            if (formula != null && !sf.formula().equalsModRenaming(formula)) {
                continue;
            } else {
                tempPioSucc = findTermInSeqFormula(sf, on, false);
                if (tempPioSucc != null) {
                    foundPositionsSucc.add(tempPioSucc);
                }
            }
        }
        if (foundPositionsAntec.size() == 1 && foundPositionsSucc.size() == 0 ||
                foundPositionsAntec.size() == 0 && foundPositionsSucc.size() == 1) {
            foundPositionsAntec.addAll(foundPositionsSucc);
            pio = foundPositionsAntec.get(0);

        } else {
            throw new ScriptException("there is more than one possible occurrence for term " + on +
                    ".\nPlease consider to additional use the parameter formula to specifiy the seuqentformula the term is in");

        }
        return pio;

    }

    /**
     * Iterate through all sequentformula and find the on term
     *
     * @param seq
     * @param toFind
     * @param inAntec
     * @return
     * @throws ScriptException
     */
    private PosInOccurrence findTermInSeqFormula(SequentFormula seq, Term toFind, boolean inAntec) throws ScriptException {
        PosInOccurrence pio = null;

        if (seq.formula().equalsModRenaming(toFind)) {
            pio = new PosInOccurrence(seq, PosInTerm.getTopLevel(), inAntec);
            //return topLevel
        } else {

            PosInTerm pit = helper(toFind, seq.formula(), PosInTerm.getTopLevel());
            if (pit != null) {
                pio = new PosInOccurrence(seq, pit, inAntec);
            }


        }
        return pio;
    }

    /**
     * go through a term and find position of toFind term in findIn term
     *
     * @param toFind
     * @param findIn
     * @param currentPos
     * @return
     * @throws ScriptException
     */
    private PosInTerm helper(Term toFind, Term findIn, PosInTerm currentPos) throws ScriptException {
        if (toFind.equalsModRenaming(findIn)) {
            return currentPos;
        }
        if (findIn.subs().isEmpty() && !toFind.equalsModRenaming(findIn)) {
            return null;
        }
        PosInTerm temp = null;
        ImmutableArray<Term> subs = findIn.subs();

        for (int i = 0; i < subs.size(); i++) {
            PosInTerm currentRound = helper(toFind, subs.get(i), currentPos.down(i));

            if (temp == null && currentRound != null) {
                temp = currentRound;
            } else {
                if (currentRound != null) {
                    throw new ScriptException("There is more than one occurrence for Term " + toFind);
                }
            }
        }
        return temp;

    }

    private List<PosInTerm> getAllMatchingPios(Term toFind, Term findIn, PosInTerm currentPos){
        List<PosInTerm> retList = new ArrayList<PosInTerm>();

        if (toFind.equalsModRenaming(findIn)) {
           retList.add(currentPos);
           return retList;
        }
        if (findIn.subs().isEmpty() && !toFind.equalsModRenaming(findIn)) {
            return retList;
        }
        
        ImmutableArray<Term> subs = findIn.subs();

        for (int i = 0; i < subs.size(); i++) {
            List<PosInTerm> currentRound = getAllMatchingPios(toFind, subs.get(i), currentPos.down(i));
            retList.addAll(currentRound);

        }
        return retList;

    }



    @Override
    public String getDocumentation() {
        return super.getDocumentation();
    }


}
