package edu.kit.iti.formal.psdbg.interpreter.funchdl;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.macros.scripts.EngineState;
import de.uka.ilkd.key.macros.scripts.RuleCommand;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import edu.kit.iti.formal.psdbg.ValueInjector;
import edu.kit.iti.formal.psdbg.interpreter.Interpreter;
import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.data.State;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.interpreter.exceptions.ScriptCommandNotApplicableException;
import edu.kit.iti.formal.psdbg.interpreter.exceptions.VariableNotDeclaredException;
import edu.kit.iti.formal.psdbg.interpreter.exceptions.VariableNotDefinedException;
import edu.kit.iti.formal.psdbg.parser.ast.CallStatement;
import edu.kit.iti.formal.psdbg.parser.ast.Variable;
import lombok.Getter;
import lombok.RequiredArgsConstructor;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.key_project.util.collection.ImmutableList;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * @author Alexander Weigl
 * @version 1 (21.05.17)
 */
@RequiredArgsConstructor
public class RuleCommandHandler implements CommandHandler<KeyData> {
    public static final String[] MAGIC_PARAMETER_NAMES = new String[]{
            "on", "formula"
    };

    private static final Logger LOGGER = LogManager.getLogger(RuleCommandHandler.class);
    @Getter
    private final Map<String, Rule> rules;

    public RuleCommandHandler() {
        this(new HashMap<>());
    }

    public static Set<String> findTaclets(Proof p, Goal g) {
        Services services = p.getServices();
        TacletFilter filter = new TacletFilter() {
            @Override
            protected boolean filter(Taclet taclet) {
                return true;
            }
        };
        RuleAppIndex index = g.ruleAppIndex();
        index.autoModeStopped();
        HashSet<String> set = new HashSet<>();
        for (SequentFormula sf : g.node().sequent().antecedent()) {
            ImmutableList<TacletApp> apps = index.getTacletAppAtAndBelow(filter,
                    new PosInOccurrence(sf, PosInTerm.getTopLevel(), true),
                    services);
            apps.forEach(t -> set.add(t.taclet().name().toString()));
        }

        try {
            for (SequentFormula sf : g.node().sequent().succedent()) {
                ImmutableList<TacletApp> apps = index.getTacletAppAtAndBelow(filter,
                        new PosInOccurrence(sf, PosInTerm.getTopLevel(), true),
                        services);
                apps.forEach(t -> set.add(t.taclet().name().toString()));
            }
        } catch (NullPointerException e) {
            e.printStackTrace();
        }
        return set;
    }

    @Override
    public boolean handles(CallStatement call, KeyData data) throws IllegalArgumentException {
        if (rules.containsKey(call.getCommand())) return true;//static/rigid rules
        try {
            if (data != null) {
                Goal goal = data.getGoal();
                Set<String> rules = findTaclets(data.getProof(), goal);
                return rules.contains(call.getCommand());
            }
        } catch (NullPointerException npe) {
            System.out.println("npe = " + npe);
            return false;
        }
        return false;
    }

    @Override
    public void evaluate(Interpreter<KeyData> interpreter,
                         CallStatement call,
                         VariableAssignment params,
                         KeyData data) throws RuntimeException, ScriptCommandNotApplicableException {
        if (!rules.containsKey(call.getCommand())) {
            throw new IllegalStateException();
        }
        //FIXME duplicate of ProofScriptCommandBuilder
        RuleCommand c = new RuleCommand();
        State<KeyData> state = interpreter.getCurrentState();
        GoalNode<KeyData> expandedNode = state.getSelectedGoalNode();
        KeyData kd = expandedNode.getData();
        Map<String, Object> map = createParameters(expandedNode.getAssignments());

        params.asMap().forEach((k, v) -> map.put(k.getIdentifier(), v.getData()));
        LOGGER.info("Execute {} with {}", call, map);
        try {
            map.put("#2", call.getCommand());
            EngineState estate = new EngineState(kd.getProof());
            estate.setGoal(kd.getNode());
            RuleCommand.Parameters cc = new RuleCommand.Parameters();
            ValueInjector valueInjector = ValueInjector.createDefault(kd.getNode());
            cc = valueInjector.inject(c, cc, map);
            AbstractUserInterfaceControl uiControl = new DefaultUserInterfaceControl();
            c.execute(uiControl, cc, estate);

            ImmutableList<Goal> ngoals = kd.getProof().getSubtreeGoals(kd.getNode());
            state.getGoals().remove(expandedNode);
            if (state.getSelectedGoalNode().equals(expandedNode)) {
                state.setSelectedGoalNode(null);
            }
            for (Goal g : ngoals) {
                KeyData kdn = new KeyData(kd, g.node());
                state.getGoals().add(new GoalNode<>(expandedNode, kdn, kdn.getNode().isClosed()));
            }
        } catch (ScriptException e) {
            if (interpreter.isStrictMode()) {
                throw new ScriptCommandNotApplicableException(e, c, map);
            } else {
                //Utils necessary oder schmeißen
                LOGGER.error("Command " + call.getCommand() + " is not applicable in line " + call.getRuleContext().getStart().getLine());
            }
        } catch (InterruptedException e) {
            e.printStackTrace();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    private Map<String, Object> createParameters(VariableAssignment assignments) {
        Map<String, Object> params = new HashMap<>();
        for (String s : MAGIC_PARAMETER_NAMES) {
            try {
                params.put(s, assignments.getValue(new Variable(Variable.MAGIC_PREFIX + s)));
            } catch (VariableNotDefinedException | VariableNotDeclaredException e) {

            }
        }
        return params;
    }

}
