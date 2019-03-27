package edu.kit.iti.formal.psdbg;

import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.api.ProofManagementApi;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.util.KeYConstants;
import edu.kit.iti.formal.psdbg.interpreter.InterpreterBuilder;
import edu.kit.iti.formal.psdbg.interpreter.KeyInterpreter;
import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.dbg.*;
import edu.kit.iti.formal.psdbg.parser.Facade;
import edu.kit.iti.formal.psdbg.parser.ast.*;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (27.10.17)
 */
public class InteractiveCLIDebugger {
    private static final Logger LOGGER = LogManager.getLogger();

    static Map<String, DebuggerCommand<KeyData>> COMMANDS = new HashMap<>();

    static {
        COMMANDS.put("r", new ReturnCommand());
        COMMANDS.put("s", new StartCommand<>(true));
        COMMANDS.put("<", new StepBackCommand<>());
        COMMANDS.put(">", new StepOverCommand<>());
        COMMANDS.put(".", new StepIntoCommand<>());
        COMMANDS.put(";", new HardStopCommand<>());
        COMMANDS.put(";", new PauseCommand<>());
    }

    private final ProofManagementApi pma;
    private final KeyInterpreter interpreter;
    private final DebuggerFramework<KeyData> df;

    public InteractiveCLIDebugger(String proof, String script) throws IOException, ProblemLoaderException, DebuggerException {
        pma = KeYApi.loadFromKeyFile(new File(proof));
        List<ProofScript> scripts = Facade.getAST(new File(script));
        InterpreterBuilder ib = new InterpreterBuilder()
                .addProofScripts(scripts)
                .proof(pma.getLoadedProof())
                .startState()
                .macros()
                .scriptCommands()
                .scriptSearchPath(new File("."));
        interpreter = ib.build();

        //ControlFlowVisitor cfgVistor = new ControlFlowVisitor(ib.getLookup());
        //MutableValueGraph<ControlFlowNode, ControlFlowTypes> cfg = cfgVistor.getGraph();

        df = new DebuggerFramework<>(interpreter, scripts.get(0), null);
        df.getStatePointerListener().add(this::printNode);
        //df.getBeforeExecutionListener().add(this::printNode);
        //df.getAfterExecutionListener().add(this::end);
        loop();
    }

    public static void main(String[] args) throws ProblemLoaderException, IOException, DebuggerException {
        System.out.println("Welcome to Psdbg with KeY" + KeYConstants.INTERNAL_VERSION);

        LOGGER.info("KeY Version: {}", KeYConstants.INTERNAL_VERSION);
        Runtime.getRuntime().addShutdownHook(new Thread(() -> LOGGER.info("Program exited")));

        new InteractiveCLIDebugger(args[0], args[1]);
    }

    private void debug() {
        //TODO write debug information
        System.out.println("digraph G {");
        for (PTreeNode<KeyData> n : df.getStates()) {
            System.out.format("%d [label=\"%s@%s (G: %d)\"]%n", n.hashCode(),
                    n.getStatement().accept(new ShortCommandPrinter()),
                    n.getStatement().getStartPosition().getLineNumber(),
                    n.getStateBeforeStmt().getGoals().size()
            );

            if (n.getStepOver() != null)
                System.out.format("%d -> %d [label=\"SO\"]%n", n.hashCode(), n.getStepOver().hashCode());
            if (n.getStepInto() != null)
                System.out.format("%d -> %d [label=\"SI\"]%n", n.hashCode(), n.getStepInto().hashCode());

            if (n.getStepInvOver() != null)
                System.out.format("%d -> %d [label=\"<SO\"]%n", n.hashCode(), n.getStepInvOver().hashCode());
            if (n.getStepInvInto() != null)
                System.out.format("%d -> %d [label=\"<SI\"]%n", n.hashCode(), n.getStepInvInto().hashCode());

            if (n.getStepReturn() != null)
                System.out.format("%d -> %d [label=\"R\"]%n", n.hashCode(), n.getStepReturn().hashCode());

        }
        System.out.println("}");
    }

    private void loop() throws DebuggerException {
        try (BufferedReader br = new BufferedReader(new InputStreamReader(System.in))) {
            while (true) {
                int counter = 0;
                while (true) {
                    boolean handled = false;
                    System.out.printf("dbg (%03d)> ", ++counter);
                    String input = br.readLine().trim().intern();
                    if (COMMANDS.containsKey(input)) {
                        handled = true;
                        try {
                            df.execute(COMMANDS.get(input));
                        } catch (DebuggerException e) {
                            if (e.isSevere())
                                throw e;
                            else {
                                System.err.println(e.getMessage());
                            }
                        }
                    }

                    //special
                    switch (input) {
                        case "!!":
                            System.exit(0);
                        case "dbg":
                            handled = true;
                            debug();
                    }

                    if (input.startsWith("b ")) {
                        handled = true;
                        setBreakpoint(Integer.parseInt(input.substring(2)));
                    }

                    if (!handled) System.err.println("Unknown command");
                }
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private void end(PTreeNode<KeyData> keyDataPTreeNode) {
        //TODO register if proof has ended!
    }

    private void printNode(PTreeNode<KeyData> node) {
        System.out.format("%3d: %s%n",
                node.getStatement().getStartPosition().getLineNumber(),
                node.getStatement().accept(new ShortCommandPrinter())
        );

        for (GoalNode<KeyData> gn : node.getStateBeforeStmt().getGoals()) {
            if (gn.equals(node.getStateBeforeStmt().getSelectedGoalNode()))
                System.out.format("\t* ");
            else
                System.out.format("\t  ");
            System.out.println(gn.getData().getNode().sequent());
        }

    }

    public void setBreakpoint(int breakpoint) {
        //df.addBreakpoint(breakpoint);
    }
}
