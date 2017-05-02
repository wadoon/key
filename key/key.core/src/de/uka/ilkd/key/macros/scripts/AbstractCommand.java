package de.uka.ilkd.key.macros.scripts;

import java.io.StringReader;
import java.util.*;
import java.util.logging.Logger;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.macros.scripts.meta.ArgumentsLifter;
import de.uka.ilkd.key.macros.scripts.meta.ProofScriptArgument;
import de.uka.ilkd.key.macros.scripts.meta.ValueInjector;
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
    private final Class<T> parameterClazz;
    protected Proof proof;
    protected Services service;
    protected EngineState state;
    protected AbstractUserInterfaceControl uiControl;

    protected static Logger log = Logger.getLogger(ProofScriptCommand.class.getName());

    public AbstractCommand(Class<T> clazz) {
        this.parameterClazz = clazz;
    }

    public List<ProofScriptArgument> getArguments() {
        if (parameterClazz == null)
            return new ArrayList<>();
        return ArgumentsLifter.inferScriptArguments(parameterClazz);
    }

    @Override public T evaluateArguments(EngineState state, Map<String, String> arguments) throws Exception {
        if (parameterClazz != null) {
            T obj = parameterClazz.newInstance();
            return state.getValueInjector().inject(obj, arguments);
        }
        return null;
    }

    @Override public void execute(AbstractUserInterfaceControl uiControl, T args, EngineState stateMap)
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

    /**
     * @param args
     * @throws ScriptException
     * @throws InterruptedException
     */
    protected void execute(T args) throws ScriptException, InterruptedException {

    }
}
