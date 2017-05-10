package de.uka.ilkd.key.api;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.macros.scripts.EngineState;
import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;
import de.uka.ilkd.key.macros.scripts.ScriptCommand;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.parser.KeYLexerF;
import de.uka.ilkd.key.parser.KeYParserF;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.match.legacy.LegacyTacletMatcher;
import org.antlr.runtime.RecognitionException;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.*;
import java.util.stream.Collectors;

/**
 * This API class offers methods to apply script commands and match commands
 *
 * @author Alexander Weigl
 * @author S. Grebing
 */
public class ScriptApi {
    private final ProofApi api;
    private final EngineState state;
    private Matcher matcher;

    public ScriptApi(ProofApi proofApi) {
        api = proofApi;
        state = new EngineState(api.getProof());
        matcher = new Matcher(api);
    }

    /**
     * Matches a sequent against a sequent pattern (a schematic sequent) returns a list of Nodes containing matching
     * results from where the information about instantiated schema variables can be extracted. If no match was possible the list is exmpt.
     * @param pattern a string representation of the pattern sequent against which the current sequent should be matched
     * @param currentSeq current concrete sequent
     * @param assignments variables appearing in the pattern as schemavariables with their corresponding type in KeY
     *
     * @return List of VariableAssignments (possibly empty if no match was found)
     */
    public List<VariableAssignments> matchPattern(String pattern, Sequent currentSeq, VariableAssignments assignments){
        return matcher.matchPattern(pattern,currentSeq,assignments);
    }

    /**
     * Execute ScriptCommand onto goal node
     *
     * @param command to be applied with parameters set
     * @return List of new proof goals (possibly empty)
     * Should throw an Exception if command not applicable?
     */
    public <T> ScriptResults executeScriptCommand(
            ProofScriptCommandCall<T> call, ProjectedNode onNode,
            VariableAssignments varsAssignment) throws ScriptException, InterruptedException {
        //TODO VariableAssignments should be in instantiateCommand

        state.setGoal(onNode.getProofNode());
        call.command.execute((AbstractUserInterfaceControl) api.getEnv().getUi(),
                call.parameter, state);

        ImmutableList<Goal> goals = api.getProof()
                .getSubtreeGoals(onNode.getProofNode());
        //TODO filter for open goals if necessary
        ScriptResults sr = new ScriptResults();

        goals.forEach(g -> sr.add(ScriptResult.create(g.node(), onNode, call)));

        return sr;
    }

    /**
     * @param arguments
     * @param <T>
     * @return
     */
    public <T> ProofScriptCommandCall<T> instantiateCommand(
            ProofScriptCommand<T> command, Map<String, String> arguments)
            throws Exception {
        return new ProofScriptCommandCall<>(command,
                command.evaluateArguments(state, arguments));
    }

    //TODO
    public void applyRule(String ruleName, String posInOcc) {
        //TacletApp app = new PosTacletApp();
        //TODO over RuleCommand
    }




    //toTerm(String, vars)

    //[(label, goal, vars)]
    //variablen klasse mit maps typen und werte linked hashmap
    //
    //chain of responsibility

    //getIntermediateTree (ScriptResults old, ScriptResults new) ~> Beweisbaum -> Shallow Copy
    //hier implementieren

    //isclosable
    //derivable : mache cut und dann auto, falls nicht schließt prune proof

    //public ProofApi openSpeculatedProof(ProjectedNode){
    //copy node + env
    // }
    /**
     * Method tries to close proof by applying the script command. If it succeeds the method returns true otherwise false.
     * In any case the proof is rolled back and the proof state is not changed visibly.
     * @param com Proof command that should close the goal
     * @param node goal node to close
     * @return true iff proof can be found using com, false otherwise
     */
    public boolean isClosable(ScriptCommand com, ProjectedNode node){


        return false;
    }

    public boolean isDerivable(String formula, ProjectedNode node){
        return false;
    }
    //new env, new PO, closable

}
