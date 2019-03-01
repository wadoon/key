package edu.kit.iti.formal.psdbg.interpreter;

import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.api.ProofApi;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import edu.kit.iti.formal.psdbg.interpreter.assignhook.InterpreterOptionsHook;
import edu.kit.iti.formal.psdbg.interpreter.assignhook.KeyAssignmentHook;
import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.interpreter.funchdl.*;
import edu.kit.iti.formal.psdbg.interpreter.matcher.KeYMatcher;
import edu.kit.iti.formal.psdbg.parser.Facade;
import edu.kit.iti.formal.psdbg.parser.Visitor;
import edu.kit.iti.formal.psdbg.parser.ast.CallStatement;
import edu.kit.iti.formal.psdbg.parser.ast.ProofScript;
import lombok.Getter;
import org.key_project.util.collection.ImmutableList;

import java.io.File;
import java.io.IOException;
import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (21.05.17)
 */

public class InterpreterBuilder {
    @Getter
    private final ProofScriptHandler psh = new ProofScriptHandler();
    @Getter
    private final MacroCommandHandler pmh = new MacroCommandHandler();
    @Getter
    private final RuleCommandHandler pmr = new RuleCommandHandler();
    @Getter
    private ProofScriptCommandBuilder pmc = new ProofScriptCommandBuilder();
    @Getter
    private BuiltInCommandHandler bich = new BuiltInCommandHandler();
    @Getter
    private ProofScript entryPoint;
    @Getter
    private Proof proof;
    @Getter
    private KeYEnvironment keyEnvironment;
    @Getter
    private HistoryListener historyLogger;
    @Getter
    private ScopeLogger logger;
    @Getter
    private DefaultLookup lookup = new DefaultLookup(psh, pmh, pmc, bich, pmr);

    @Getter
    private KeyAssignmentHook keyHooks = new KeyAssignmentHook();

    private KeyInterpreter interpreter = new KeyInterpreter(lookup);



    @Getter
    private InterpreterOptionsHook<KeyData> optionsHook = new InterpreterOptionsHook<>(interpreter);

    public InterpreterBuilder addProofScripts(File file) throws IOException {
        return addProofScripts(Facade.getAST(file));
    }

    public InterpreterBuilder addProofScripts(List<ProofScript> ast) {
        psh.addScripts(ast);
        return this;
    }

    public InterpreterBuilder startWith(ProofScript entryPoint) {
        this.entryPoint = entryPoint;
        return this;
    }

    public KeyInterpreter build() {
        interpreter.getVariableHooks().add(keyHooks);
        interpreter.getVariableHooks().add(optionsHook);
        return interpreter;
    }

    public InterpreterBuilder scriptSearchPath(File... paths) {
        psh.getSearchPath().addAll(Arrays.asList(paths));
        return this;
    }

    public InterpreterBuilder proof(KeYEnvironment env, Proof proof) {
        this.keyEnvironment = env;
        this.proof = proof;
        return proof(new ProofApi(proof, env));
    }

    public InterpreterBuilder scriptCommands() {
        return scriptCommands(KeYApi.getScriptCommandApi().getScriptCommands());
    }

    public InterpreterBuilder scriptCommands(Collection<ProofScriptCommand> commands) {
        commands.forEach(m -> pmc.getCommands().put(m.getName(), m));
        return this;
    }

    public InterpreterBuilder macros() {
        return macros(KeYApi.getMacroApi().getMacros());
    }

    public InterpreterBuilder macros(Collection<ProofMacro> macros) {
        macros.forEach(m -> pmh.getMacros().put(m.getScriptCommandName(), m));
        return this;
    }

    public InterpreterBuilder addKeyMatcher(ProofApi api) {
        interpreter.setMatcherApi(new KeYMatcher(api.getEnv().getServices()));
        return this;
    }

    public InterpreterBuilder register(ProofScript... script) {
        psh.addScripts(Arrays.asList(script));
        return this;
    }

    public InterpreterBuilder onEntry(Visitor v) {
        interpreter.getEntryListeners().add(0, v);
        return this;
    }


    public InterpreterBuilder onExit(Visitor v) {
        interpreter.getExitListeners().add(v);
        return this;
    }


    public InterpreterBuilder captureHistory() {
        if (historyLogger == null)
            historyLogger = new HistoryListener(interpreter);
        return onEntry(historyLogger);
    }


    public InterpreterBuilder log(String prefix) {
        if (logger == null)
            logger = new ScopeLogger("interpreter");
        return onEntry(logger);
    }

    public InterpreterBuilder proof(ProofApi pa) {
        addKeyMatcher(pa);
        pa.getRules().forEach(s -> pmr.getRules().put(s, null));
        keyEnvironment = pa.getEnv();
        proof = pa.getProof();
        return this;
    }

    public InterpreterBuilder setScripts(List<ProofScript> scripts) {
        psh.getScripts().clear();
        return addProofScripts(scripts);
    }

    public InterpreterBuilder inheritState(Interpreter<KeyData> interpreter) {
        this.interpreter.pushState(interpreter.peekState());
        return this;
    }

    public InterpreterBuilder ignoreLines(Set<Integer> lines) {
        CommandHandler<KeyData> ignoreHandler = new CommandHandler<KeyData>() {
            @Override
            public boolean handles(CallStatement call, KeyData data) throws IllegalArgumentException {
                return lines.contains(call.getStartPosition().getLineNumber());
            }

            @Override
            public void evaluate(Interpreter<KeyData> interpreter, CallStatement call, VariableAssignment params, KeyData data) {
                //System.out.println("InterpreterBuilder.evaluate");
            }
        };
        lookup.getBuilders().add(0, ignoreHandler);
        return this;
    }

    public InterpreterBuilder ignoreLinesUntil(final int caretPosition) {
        CommandHandler<KeyData> ignoreHandler = new CommandHandler<KeyData>() {
            @Override
            public boolean handles(CallStatement call, KeyData data) throws IllegalArgumentException {
                return call.getRuleContext().getStart().getStartIndex() < caretPosition;
            }

            @Override
            public void evaluate(Interpreter<KeyData> interpreter, CallStatement call, VariableAssignment params, KeyData data) {
                System.out.println("InterpreterBuilder.evaluate");
            }
        };
        lookup.getBuilders().add(0, ignoreHandler);
        return this;
    }

    public InterpreterBuilder startState() {
        if (proof == null || keyEnvironment == null)
            throw new IllegalStateException("Call proof(..) before startState");


        ImmutableList<Goal> openGoals = proof.getSubtreeGoals(proof.root());
        List<GoalNode<KeyData>> goals = openGoals.stream().map(g ->
                new GoalNode<>(new KeyData(g, keyEnvironment, proof)))
                .collect(Collectors.toList());


        interpreter.newState(goals);


        return this;

    }

    private InterpreterBuilder startState(GoalNode<KeyData> startGoal) {
        interpreter.newState(startGoal);

        return this;
    }

    public InterpreterBuilder setProblemPath(File path){
        Map<String, CommandHandler<KeyData>> builtinsnew = this.bich.getBuiltins();

        builtinsnew.put(SaveCommand.SAVE_COMMAND_NAME, new SaveCommand(path));
        this.bich.setBuiltins(builtinsnew);

        return this;

    }

}
