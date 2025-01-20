/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.ServiceLoader;
import java.util.function.Consumer;

/**
 * @author Mattias Ulbrich
 * @author Alexander Weigl
 */
public class ProofScriptEngine {
    private static final Map<String, ProofScriptCommand<?>> COMMANDS = loadCommands();
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofScriptEngine.class);

    private final KeyAst.ProofScriptEntry script;

    /**
     * The initially selected goal.
     */
    private final Goal initiallySelectedGoal;

    /**
     * The engine state map.
     */
    private EngineState stateMap;

    private Consumer<Message> commandMonitor;

    public ProofScriptEngine(KeyAst.ProofScriptEntry file) throws IOException {
        this.script = file;
        this.initiallySelectedGoal = null;
    }

    /**
     * Instantiates a new proof script engine.
     *
     * @param script                the script
     * @param initiallySelectedGoal the initially selected goal
     */
    public ProofScriptEngine(KeyAst.ProofScriptEntry script, Goal initiallySelectedGoal) {
        this.script = script;
        this.initiallySelectedGoal = initiallySelectedGoal;
    }

    private static Map<String, ProofScriptCommand<?>> loadCommands() {
        Map<String, ProofScriptCommand<?>> result = new HashMap<>();
        var loader = ServiceLoader.load(ProofScriptCommand.class);

        for (ProofScriptCommand<?> cmd : loader) {
            result.put(cmd.getName(), cmd);
        }

        return result;
    }

    public void execute(AbstractUserInterfaceControl uiControl, Proof proof)
            throws IOException, InterruptedException, ScriptException {
        stateMap = new EngineState(proof, this);

        if (initiallySelectedGoal != null) {
            stateMap.setGoal(initiallySelectedGoal);
        }

        // add the filename (if available) to the statemap.
        var uri = script.getStartLocation().fileUri();
        if (uri != null) {
            stateMap.setBaseFileName(Paths.get(uri).toFile());
        }
        // add the observer (if installed) to the state map
        if (commandMonitor != null) {
            stateMap.setObserver(commandMonitor);
        }

        var proofScript = script.get().proofScriptCommand();
        execute(uiControl, proof, proofScript);
    }

    @SuppressWarnings("unchecked")
    void execute(AbstractUserInterfaceControl uiControl, Proof proof, List<KeYParser.ProofScriptCommandContext> proofScript) throws InterruptedException, ScriptException {
        int cnt = 0;
        ParseTreeVisitor<Object> valueEvaluator = new ExprEvaluator(proof.getServices(), proof.getNamespaces());

        for (var cmd : proofScript) {
            if (Thread.interrupted()) {
                throw new InterruptedException();
            }

            /*String cmd = "'" + argMap.get(ParsedCommand.LITERAL_KEY) + "'";
            if (cmd.length() > MAX_CHARS_PER_COMMAND) {
                cmd = cmd.substring(0, MAX_CHARS_PER_COMMAND) + " ...'";
            }*/

            String name = cmd.cmd.getText();
            var argMap = new HashMap<String, Object>();
            var paramCount = 2;
            for (var param : cmd.proofScriptParameters().proofScriptParameter()) {
                var argName = param.pname == null ? "#" + paramCount++ : param.pname.getText();
                argMap.put(argName, param.expr.accept(valueEvaluator));
            }
            argMap.put(ParsedCommand.COMMAND_KEY, name);

            if (cmd.sub != null) {
                argMap.put(ParsedCommand.KEY_SUB_SCRIPT, cmd.sub);
            }

            var hasSystemCommandPrefix = null != cmd.AT();

            final Node firstNode = stateMap.getFirstOpenAutomaticGoal().node();
            Location start = Location.fromToken(cmd.start);
            if (commandMonitor != null && stateMap.isEchoOn() && !hasSystemCommandPrefix) {
                commandMonitor.accept(new ExecuteInfo(name, start, firstNode.serialNr()));
            }

            try {

                ProofScriptCommand<Object> command = (ProofScriptCommand<Object>) COMMANDS.get(name);
                if (command == null) {
                    throw new ScriptException("Unknown command: " + name);
                }


                Object o = command.evaluateArguments(stateMap, argMap);
                if (!hasSystemCommandPrefix && stateMap.isEchoOn()) {
                    LOGGER.debug("[{}] goal: {}, source line: {}, command: {}", ++cnt,
                            firstNode.serialNr(), start, cmd);
                }
                command.execute(uiControl, o, stateMap);
                firstNode.getNodeInfo().setScriptRuleApplication(true);
            } catch (InterruptedException ie) {
                throw ie;
            } catch (ProofAlreadyClosedException e) {
                if (stateMap.isFailOnClosedOn()) {
                    throw new ScriptException(
                            String.format(
                                    """
                                            Proof already closed while trying to fetch next goal.
                                            This error can be suppressed by setting '@failonclosed off'.
                                            
                                            Command: %s
                                            Line:%d
                                            """,
                                    argMap.get(ParsedCommand.LITERAL_KEY), start.getPosition().line()),
                            start, e);
                } else {
                    LOGGER.info(
                            "Proof already closed at command \"{}\" at line %d, terminating in line {}",
                            argMap.get(ParsedCommand.LITERAL_KEY), start.getPosition().line());
                    break;
                }
            } catch (Exception e) {
                LOGGER.debug("GOALS: {}", proof.getSubtreeGoals(proof.root()).size());
                proof.getSubtreeGoals(stateMap.getProof().root())
                        .forEach(g -> LOGGER.debug("{}", g.sequent()));
                throw new ScriptException(
                        String.format("Error while executing script: %s\n\nCommand: %s", e.getMessage(),
                                argMap.get(ParsedCommand.LITERAL_KEY)),
                        start, e);
            }
        }
    }

    public EngineState getStateMap() {
        return stateMap;
    }

    /**
     * Set the routine that is executed before every successfully executed command.
     *
     * @param monitor the monitor to set
     */
    public void setCommandMonitor(Consumer<Message> monitor) {
        this.commandMonitor = monitor;
    }

    public static ProofScriptCommand<?> getCommand(String commandName) {
        return COMMANDS.get(commandName);
    }

    public interface Message {
    }

    public record EchoMessage(String message) implements Message {
    }

    public record ExecuteInfo(String command, Location location, int nodeSerial) implements Message {
    }
}
