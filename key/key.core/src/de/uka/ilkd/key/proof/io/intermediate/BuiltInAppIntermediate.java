/**
 * 
 */
package de.uka.ilkd.key.proof.io.intermediate;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.calculus.PosInTerm;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.Pair;

import de.uka.ilkd.key.logic.JavaDLTerm;

/**
 * Encapsulates intermediate information for constructing a built-in rule application.
 *
 * @author Dominic Scheurer
 */
public class BuiltInAppIntermediate extends AppIntermediate {

    private String ruleName = null;
    private Pair<Integer, PosInTerm<JavaDLTerm>> posInfo = null;
    private String contract = null;
    private ImmutableList<Pair<Integer, PosInTerm<JavaDLTerm>>> builtInIfInsts = null;
    private ImmutableList<Name> newNames = null;

    public BuiltInAppIntermediate(String ruleName,
            Pair<Integer, PosInTerm<JavaDLTerm>> pos, String contract,
            ImmutableList<Pair<Integer, PosInTerm<JavaDLTerm>>> builtInIfInsts,
            ImmutableList<Name> newNames) {
        this.ruleName = ruleName;
        this.posInfo = pos;
        this.contract = contract;
        this.builtInIfInsts = builtInIfInsts;
        this.newNames = newNames;
    }

    public String getRuleName() {
        return ruleName;
    }

    public Pair<Integer, PosInTerm<JavaDLTerm>> getPosInfo() {
        return posInfo;
    }

    public String getContract() {
        return contract;
    }

    public ImmutableList<Pair<Integer, PosInTerm<JavaDLTerm>>> getBuiltInIfInsts() {
        return builtInIfInsts;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.io.intermediate.AppIntermediate#getNewNames()
     */
    @Override
    public ImmutableList<Name> getNewNames() {
        return newNames;
    }

}
