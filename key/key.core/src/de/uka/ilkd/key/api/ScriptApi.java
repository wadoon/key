package de.uka.ilkd.key.api;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.scripts.EngineState;
import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;
import de.uka.ilkd.key.macros.scripts.ScriptException;

import java.util.List;
import java.util.Map;

/**
 * Created by sarah on 4/5/17.
 *
 * @author Alexander Weigl
 */
public class ScriptApi {
    private final ProofApi api;
    private final EngineState state;

    public ScriptApi(ProofApi proofApi) {
        api = proofApi;
        state = new EngineState(api.getProof());
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
        call.command.execute((AbstractUserInterfaceControl) api.getEnv().getUi(),
                call.parameter, state);
        return null; // TODO
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

    //matching Seq Term: matchResult
    //
    //toTerm(String, vars)

    //[(label, goal, vars)]
    //variablen klasse mit maps typen und werte linked hashmap
    //
    //chain of responsibility

    //getIntermediateTree (ScriptResults old, ScriptResults new) ~> Beweisbaum -> Shallow Copy
    //hier implementieren

    //isclosable
    //derivable : mache cut und dann auto, falls nicht schließt prune proof

}
