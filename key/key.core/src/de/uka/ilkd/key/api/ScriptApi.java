package de.uka.ilkd.key.api;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;
import de.uka.ilkd.key.proof.Node;

import java.util.List;

/**
 * Created by sarah on 4/5/17.
 */
public abstract class ScriptApi {
    private KeYEnvironment env;
    /**
     * Execute ScriptCommand onto goal node
     * @param command to be applied with parameters set
     * @return List of new proof goals (possibly empty)
     * Should throw an Exception if command not applicable?
     */
    public abstract List<Node> executeScriptCommand(ProofScriptCommand command, Node goal, KeYEnvironment env);

    //matching Seq Term
    // goal, variableAss
    //[(label, goal, vars)]
    //variablen klasse mit maps typen und werte linked hashmap
    //
    //toTerm(String, vars)
    //chain

    //getIntermediateTree (ScriptResults old, ScriptResults new) ~> Beweisbaum -> Shallow Copy

    //Interface für proof nodes projectionNode

    //isclosable
    //derivable : mache cut und dann auto, fallls nicht schließt prune proof


}
