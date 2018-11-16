/**
 *
 */
package de.uka.ilkd.key.proof.io.intermediate;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.rule.lazyse.InstantiateLoopHoleRule;
import de.uka.ilkd.key.util.Pair;

/**
 * Encapsulates intermediate information for constructing a
 * {@link InstantiateLoopHoleRule} application.
 *
 * @author Dominic Scheurer
 */
public class InstantiateLoopHoleRuleAppIntermediate
        extends BuiltInAppIntermediate {

    private final String pathCPH;
    private final String pathCInst;
    private final String symbStPH;
    private final String symbStInst;

    public InstantiateLoopHoleRuleAppIntermediate(Pair<Integer, PosInTerm> pos,
            ImmutableList<Name> newNames, String pathCPH, String pathCInst,
            String symbStPH, String symbStInst) {
        super(InstantiateLoopHoleRule.INSTANCE.displayName(), pos, null, null,
            newNames);

        this.pathCPH = pathCPH;
        this.pathCInst = pathCInst;
        this.symbStPH = symbStPH;
        this.symbStInst = symbStInst;
    }

    public String getPathCPH() {
        return pathCPH;
    }

    public String getPathCInst() {
        return pathCInst;
    }

    public String getSymbStPH() {
        return symbStPH;
    }

    public String getSymbStInst() {
        return symbStInst;
    }
}
