package de.uka.ilkd.key.api;

import de.uka.ilkd.key.control.KeYEnvironment;

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
    //public abstract List<ProjectedNode> executeScriptCommand(ProofScriptCommand command (Parameter?), ProjectNode pn, varsAssignment, KeYEnvironment env);

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
