package de.uka.ilkd.key.api;

import de.uka.ilkd.key.macros.scripts.ScriptCommand;

import java.util.List;
import java.util.Set;

/**
 * Object that represents one result goal of a script command
 * It holds a reference to its parent node and to the list of variables and their values for this result
 * Created by S. Grebing
 */
public class ScriptResult {

    /**
     * The current goal node
     */
    private ProjectedNode newNode;

    /**
     * the parent scriptNode to which the scriptcommand was applied
     */
    private ProjectedNode parentNode;

    /**
     * The scriptcommand that lead to this result
     */
    private ScriptCommand command;

    /**
     * The reference to the varaibleassingments for this result
     */
    //private VariableAssignemnts assignment;

    /**
     * The list of labels for the result
     */
    private List<Set<String>>  labels;

    public ScriptResult(){

    }

}
