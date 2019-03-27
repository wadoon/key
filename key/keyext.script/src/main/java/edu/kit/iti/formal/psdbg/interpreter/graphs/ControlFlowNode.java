package edu.kit.iti.formal.psdbg.interpreter.graphs;

import edu.kit.iti.formal.psdbg.parser.ast.ASTNode;
import lombok.Data;

/**
 * ControlFlowNode for ControlFlowGraph to look up step-edges for the debugger.
 */
@Data
public class ControlFlowNode {
    /**
     * Statement node
     */
    private final ASTNode scriptstmt;

    /**
     * Call context
     */
    private ASTNode[] callCtx;
}
