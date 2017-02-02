package de.uka.ilkd.key.rule.join.procedures;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.join.JoinProcedure;

/**
 * TODO
 *
 * @author Dominic Scheurer
 */
public abstract class JoinParams {
    private Class<? extends JoinProcedure> joinProc;

    public JoinParams(Class<? extends JoinProcedure> joinProc) {
        this.joinProc = joinProc;
    }

    public Class<? extends JoinProcedure> getJoinProc() {
        return joinProc;
    }

    /**
     * TODO
     * 
     * @return
     */
    public Class<? extends JoinProcedure> getJoinProcedure() {
        return joinProc;
    }

    /**
     * TODO
     * 
     * @param services
     * @return
     */
    public abstract JoinProcedure getInstantiatedJoinProcedure(Services services);
}