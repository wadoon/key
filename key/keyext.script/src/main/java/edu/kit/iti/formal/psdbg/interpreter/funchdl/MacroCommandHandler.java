package edu.kit.iti.formal.psdbg.interpreter.funchdl;

import com.google.common.io.CharStreams;
import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Goal;
import edu.kit.iti.formal.psdbg.interpreter.Interpreter;
import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.data.State;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.parser.ast.CallStatement;
import lombok.Getter;
import lombok.RequiredArgsConstructor;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.key_project.util.collection.ImmutableList;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (21.05.17)
 */
@RequiredArgsConstructor
public class MacroCommandHandler implements CommandHandler<KeyData> {
    protected static Logger LOGGER = LogManager.getLogger(MacroCommandHandler.class);

    @Getter
    private final Map<String, ProofMacro> macros;

    public MacroCommandHandler() {
        macros = new HashMap<>();
    }

    public MacroCommandHandler(Collection<ProofMacro> macros) {
        this();
        macros.forEach(m -> this.macros.put(m.getScriptCommandName(), m));
    }


    @Override
    public boolean handles(CallStatement call, KeyData data) throws IllegalArgumentException {
        return macros.containsKey(call.getCommand());
    }

    @Override
    public void evaluate(Interpreter<KeyData> interpreter,
                         CallStatement call,
                         VariableAssignment params, KeyData data) {
        long startTime = System.currentTimeMillis();

        //ProofMacro m = macros.get(call.getCommand());
        ProofMacro macro = KeYApi.getMacroApi().getMacro(call.getCommand());
        /*ProofMacroFinishedInfo info = ProofMacroFinishedInfo.getDefaultInfo(macro,
                interpreter.getCurrentState().getSelectedGoalNode().getData().getProof());
        */

        State<KeyData> state = interpreter.getCurrentState();
        GoalNode<KeyData> expandedNode = state.getSelectedGoalNode();
        assert state.getGoals().contains(expandedNode);


        try {
            //uiControl.taskStarted(new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Macro, macro.getName(), 0));
            synchronized (macro) {
                AbstractUserInterfaceControl uiControl = new DefaultUserInterfaceControl();
                macro.applyTo(uiControl, expandedNode.getData().getNode(), null, uiControl);
                ImmutableList<Goal> ngoals = expandedNode.getData().getProof().getSubtreeGoals(expandedNode.getData().getNode());
                state.getGoals().remove(expandedNode);
                state.setSelectedGoalNode(null);
                if (!ngoals.isEmpty()) {
                    ngoals.stream()
                            .map(g -> new KeyData(expandedNode.getData(), g))
                            .map(kd -> new GoalNode<>(expandedNode, kd, false))
                            .forEachOrdered(gn -> state.getGoals().add(gn));
                    assert !state.getGoals().contains(expandedNode);
                }
            }
        } catch (Exception e) {
            e.printStackTrace();
        } finally {
            LOGGER.debug("Execution of {} took {} ms", call.getCommand(), (System.currentTimeMillis() - startTime));
        }
    }

    @Override
    public String getHelp(CallStatement call) {
        ProofMacro macro = macros.get(call.getCommand());
        System.out.println(getClass().getPackage());

        InputStream res = getClass().getResourceAsStream("/psdbg/macros/" + call.getCommand() + ".html");
        System.out.println("res = " + res);
        try {
            return CharStreams.toString(new InputStreamReader(res, "utf-8"));
        } catch (NullPointerException | IOException e) {
            return "No Help found for " + call.getCommand();

        }


    }
}
