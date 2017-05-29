/**
 * 
 */
package de.uka.ilkd.key.proof.io.intermediate;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.util.Pair;

/**
 * Encapsulates intermediate information for constructing a built-in rule application.
 *
 * @author Dominic Scheurer
 */
public class BuiltInAppIntermediate extends AppIntermediate {

    private String ruleName = null;
    private Pair<Integer, PosInTerm> posInfo = null;
    private String contract = null;
    private ImmutableList<Pair<Integer, PosInTerm>> builtInIfInsts = null;
    private ImmutableList<Name> newNames = null;
    private String invTerm = null;
    private String currLocalOuts = null;

    public BuiltInAppIntermediate(String ruleName,
            Pair<Integer, PosInTerm> pos, String contract,
            ImmutableList<Pair<Integer, PosInTerm>> builtInIfInsts,
            ImmutableList<Name> newNames, String invTerm, String currLocalOuts) {
        this.ruleName = ruleName;
        this.posInfo = pos;
        this.contract = contract;
        this.builtInIfInsts = builtInIfInsts;
        this.newNames = newNames;
        this.invTerm = invTerm;
        this.currLocalOuts = currLocalOuts;
    }

    public String getRuleName() {
        return ruleName;
    }

    public Pair<Integer, PosInTerm> getPosInfo() {
        return posInfo;
    }

    public String getContract() {
        return contract;
    }

    public ImmutableList<Pair<Integer, PosInTerm>> getBuiltInIfInsts() {
        return builtInIfInsts;
    }
    
    public String getInvTerm() {
        return invTerm;
    }
    
    public String getCurrLocalOuts() {
        return currLocalOuts;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.io.intermediate.AppIntermediate#getNewNames()
     */
    @Override
    public ImmutableList<Name> getNewNames() {
        return newNames;
    }

}
