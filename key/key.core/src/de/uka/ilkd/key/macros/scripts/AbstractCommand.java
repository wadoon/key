package de.uka.ilkd.key.macros.scripts;

import java.io.StringReader;
import java.util.Deque;
import java.util.LinkedList;
import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofSettings;

/**
 * <p><b>Inheritance:</b></p>
 *
 * @param <T>
 * @author Alexander Weigl
 */
public abstract class AbstractCommand<T> implements ProofScriptCommand<T> {

    protected Proof proof;
    protected Services service;
    protected EngineState state;
    protected AbstractUserInterfaceControl uiControl;

    @Override public void execute(AbstractUserInterfaceControl uiControl,
            T args, EngineState stateMap)
            throws ScriptException, InterruptedException {
        proof = stateMap.getProof();
        service = proof.getServices();
        state = stateMap;
        this.uiControl = uiControl;

        try {
            execute(args);
        }
        finally {
            //preventing memory leak
            proof = null;
            service = null;
            state = null;
        }
    }

    public abstract void execute(T args)
            throws ScriptException, InterruptedException;
}
