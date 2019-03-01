package edu.kit.iti.formal.psdbg.interpreter.dbg;

import com.google.common.graph.MutableValueGraph;
import edu.kit.iti.formal.psdbg.interpreter.graphs.ControlFlowNode;
import edu.kit.iti.formal.psdbg.interpreter.graphs.ControlFlowTypes;
import lombok.Getter;
import lombok.Setter;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Consumer;
import java.util.stream.Collectors;

/**
 * Class controlling and maintaining proof tree structure for debugger
 * and handling step functions for the debugger
 *
 * @author S. Grebing
 */
public class ProofTreeManager<T> {
    private static final Logger LOGGER = LogManager.getLogger(ProofTreeManager.class);

    @Getter
    private final List<Consumer<PTreeNode<T>>> statePointerListener = new ArrayList<>(2);

    /*
    @Nonnull
    @Getter
    private final MutableValueGraph<PTreeNode, ControlFlowTypes> graph =
            ValueGraphBuilder.directed().allowsSelfLoops(false).build();
    */

    @Getter
    @Setter
    @Nullable
    private final MutableValueGraph<ControlFlowNode, ControlFlowTypes> controlFlowGraph;

    @Getter
    private final Set<PTreeNode<T>> nodes = new HashSet<>();

    @Getter @Setter
    private boolean suppressStatePointerListener = false;

    /**
     * Counting the receive order of {@link PTreeNode}
     */
    @Getter @Setter
    private AtomicInteger counter = new AtomicInteger();

    /**
     * Pointer to current selected state in graph
     */
    @Nullable
    private PTreeNode<T> statePointer;

    private List<List<PTreeNode<T>>> context = new ArrayList<>(10);

    public ProofTreeManager(MutableValueGraph<ControlFlowNode, ControlFlowTypes> controlFlowGraph) {
        this.controlFlowGraph = controlFlowGraph;
        pushContext();
    }

    /**
     * This method handles the insertion of new nodes into graph.
     *
     * @param node
     */
    public void receiveNode(@Nonnull PTreeNode<T> node) {
        node.setOrder(counter.incrementAndGet());
        LOGGER.info("Tree received new node: {}", node);
        //we got a deeper in the AST
        int ctxLength = node.getContext().length;

        // We got a step deeper in the ASTNode stack.
        // So we have a caller
        if (getContextDepth() < ctxLength) {
            pushContext();
            intoCurrentContext(node);
            // step into happens
            assert statePointer != null : "We are in a sub context, so where had to be a statePointer!";
            statePointer.connectStepInto(node);
        }

        // Same depth means, we are working on a StatementList
        // all are connected at least by StepOver
        //  // if the last ASTNode was atomic, this is also a StepInto
        if (getContextDepth() == ctxLength) {
            intoCurrentContext(node);
            if (statePointer != null) {
                statePointer.connectStepOver(node);
                //if (statePointer.isAtomic())
                //    statePointer.setStepInto(node);
            }
        }

        // We became an level upwards, so we have left an context.
        // Maintain, StepReturn and StepOver
        if (getContextDepth() > ctxLength) {
            popContext(node); // maintains StepReturn for every Node in popped context
            assert statePointer != null : "Not possible, we are in a callee, so there must be a parent in the context";

            /* The situation on the context stack:

                            __________ popped context
               (ctx a b c d (ctx d e f) g
                          ^          ^  ^ node
                          |          | StatePointer
                          | prevCtx, the ASTNode who creates the ctx (foreach, repeat, case,...)
             */

            statePointer.setStepOver(node);
            //node.setStepBack(statePointer);

            PTreeNode<T> prevCtx = getNodeOnContext(-1);
            prevCtx.connectStepOver(node);

            /*if (statePointer.isAtomic())
                statePointer.setStepInto(node);
                */
        }


        nodes.add(node);
        setStatePointer(node);
    }

    //region context management
    private PTreeNode<T> getNodeOnContext(int pos) {
        return peekContext().get(pos < 0 ? peekContext().size() + pos : pos);
    }

    private List<PTreeNode<T>> peekContext() {
        return context.get(context.size() - 1);
    }

    private void popContext(PTreeNode<T> node) {
        for (PTreeNode<T> subs : context.get(context.size() - 1)) {
            subs.setStepReturn(node);
        }
        context.remove(context.size() - 1);
    }

    private void intoCurrentContext(PTreeNode<T> node) {
        context.get(context.size() - 1).add(node);
    }

    private void pushContext() {
        List<PTreeNode<T>> nl = new LinkedList<>();
        context.add(nl);
    }

    public int getContextDepth() {
        return (getStatePointer() == null) ? 0 : getStatePointer().getContext().length;
    }
    //endregion

    @Nullable
    public PTreeNode<T> getStatePointer() {
        return statePointer;
    }

    public void setStatePointer(@Nullable PTreeNode<T> statePointer) {
        this.statePointer = statePointer;
        fireStatePointerChanged();
    }

    protected void fireStatePointerChanged() {
        if (!suppressStatePointerListener)
            statePointerListener.forEach(l -> l.accept(statePointer));
    }

    public PTreeNode getStartNode() {
        Iterator<PTreeNode<T>> iterator = nodes.iterator();
        if (iterator.hasNext()) {

            PTreeNode currentnode = iterator.next();

            while (! (currentnode.getStepInvOver() == null && currentnode.getStepInvInto() == null)) {
                currentnode = (currentnode.getStepInvOver() != null) ? currentnode.getStepInvOver() : currentnode.getStepInvInto();

            }
            return currentnode;
        }

        return null;
    }

    public List<PTreeNode<T>> getNarrowNodesToTextPosition(int textPosition) {
        synchronized (nodes) {
            List<PTreeNode<T>> candidates = nodes.stream()
                    // filter by the context
                    .filter(n ->
                            n.getStatement().getRuleContext().start.getStartIndex() <= textPosition &&
                                    textPosition <= n.getStatement().getRuleContext().stop.getStopIndex())
                    .collect(Collectors.toList());

            Comparator<PTreeNode<T>> widthCmp = Comparator.comparingInt(PTreeNode::getSyntaxWidth);
            Comparator<PTreeNode<T>> orderCmp = Comparator.comparingInt(PTreeNode::getOrder);

            candidates.sort((o1, o2) -> {
                int cmp = widthCmp.compare(o1, o2);
                if (cmp == 0)
                    return orderCmp.compare(o1, o2);
                return cmp;
            });
            return candidates;
        }
    }
}
