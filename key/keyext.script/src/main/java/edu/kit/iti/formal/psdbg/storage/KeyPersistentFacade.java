package edu.kit.iti.formal.psdbg.storage;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.data.State;

import javax.xml.bind.JAXBException;
import java.io.IOException;
import java.io.Reader;
import java.io.Writer;

/**
 * @author Alexander Weigl
 * @version 1 (16.05.18)
 */
public class KeyPersistentFacade {
    public static void write(State<KeyData> state, Writer fw) throws IOException, JAXBException {
        PersistentState ps = new PersistentState();
        for (GoalNode<KeyData> gn : state.getGoals()) {
            PersistentGoal pg = new PersistentGoal();
            pg.setGoalIdentifier(WalkableLabelFacade.getCompressedWalkableLabel(gn.getData().getNode()));
            pg.setSelected(gn == state.getSelectedGoalNode());
            gn.getAssignments().asMap().forEach((a, b) -> {
                pg.addVariable(a.getIdentifier(),
                        b.getType().toString(),
                        b.getData().toString());

            });
            ps.getGoals().add(pg);
        }
        PersistentFacade.write(ps, fw);
    }

    public static State<KeyData> read(KeYEnvironment env, Proof proof, Reader reader)
            throws JAXBException {
        PersistentState ps = PersistentFacade.read(reader);
        State<KeyData> state = new State<>();
        for (PersistentGoal pg : ps.getGoals()) {
            Node node = WalkableLabelFacade.findNode(proof, pg.getGoalIdentifier());
            Goal goal = proof.getGoal(node);
            KeyData kd = new KeyData(goal, env, proof);
            GoalNode<KeyData> gn = new GoalNode<>(kd);
            state.getGoals().add(gn);
            if (pg.isSelected())
                state.setSelectedGoalNode(gn);
        }
        return state;
    }
}
