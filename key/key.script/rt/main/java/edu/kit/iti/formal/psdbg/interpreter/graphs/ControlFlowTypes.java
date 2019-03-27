package edu.kit.iti.formal.psdbg.interpreter.graphs;

/**
 * Edge Type a state graph and control flow graph may have
 */
public enum ControlFlowTypes {
    STEP_INTO, STEP_OVER, STEP_BACK, STEP_RETURN, STEP_OVER_COND, STATE_FLOW;
}
