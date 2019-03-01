package edu.kit.iti.formal.psdbg;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import lombok.val;
import org.apache.commons.lang.ArrayUtils;
import org.key_project.util.collection.ImmutableList;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * Utillities for producing labels of KeY proof nodes
 *
 * @author Alexander Weigl
 * @see edu.kit.iti.formal.psdbg.interpreter.data.KeyData
 * @see Node
 */
public class LabelFactory {
    public static String SEPARATOR = " // ";

    public static String RANGE_SEPARATOR = " -- ";

    public static String END_MARKER = "$$";

    /**
     * Create Label for goalview according to function that is passed.
     * The following functions can be given:
     * <ul>
     * <li>@see  #Method getRuleLabel()</li>
     * <li>@see  #Method getBranchingLabel()</li>
     * <li>@see  #Method getNameLabel()</li>
     * <li>@see  #Method getProgramLinesLabel()</li>
     * <li>@see  #Method getProgramStatementsLabel()</li>
     * </ul>
     *
     * @param projection function determining which kind of label to construct
     * @return Label from this node to parent
     */
    private static String constructLabel(Node cur, Function<Node, String> projection) {
        StringBuilder sb = new StringBuilder();
        do {
            try {
                String section = projection.apply(cur);
                //filter null elements and -1 elements
                if (section != null && !(section.equals(Integer.toString(-1)))) {
                    sb.append(section);
                    sb.append(SEPARATOR);

                }
            } catch (Exception e) {
            }
            cur = cur.parent();
        } while (cur != null);
        sb.append(END_MARKER);
        return sb.toString();
    }

    public static String getBranchingLabel(Node node) {
        StringBuilder sb = new StringBuilder();
        while (node != null) {
            val p = node.parent();
            if (p != null && p.childrenCount() != 1) {
                val branchLabel = node.getNodeInfo().getBranchLabel();
                sb.append(branchLabel != null && !branchLabel.isEmpty()
                        ? branchLabel
                        : "#" + p.getChildNr(node))
                        .append(SEPARATOR);
            }
            node = p;
        }
        sb.append(END_MARKER);
        return sb.toString();
    }

    public static String getNameLabel(Node node) {
        return constructLabel(node, Node::name);
    }

    public static String getRuleLabel(Node node) {
        return constructLabel(node, (n) -> n.getAppliedRuleApp().rule().name().toString());
    }

    public static String getProgramLines(Node node) {
        return constructLabel(node, n -> {
            int startPos = n.getNodeInfo().getActiveStatement().getPositionInfo().getStartPosition().getLine();
            int endPos = n.getNodeInfo().getActiveStatement().getPositionInfo().getEndPosition().getLine();
            if (startPos == endPos) {
                return Integer.toString(startPos);
            } else {
                String start = Integer.toString(startPos);
                String end = Integer.toString(endPos);
                return start + RANGE_SEPARATOR + end;
            }
        });
    }

    public static String getProgramStatmentLabel(Node node) {
        return constructLabel(node, n ->
                n.getNodeInfo().getFirstStatementString());
    }

    public static List<String[]> getLabelOfOpenGoals(Proof root, Function<Node, String> func) {
        if (root.closed())
            return Collections.emptyList();
        ImmutableList<Goal> open = root.getSubtreeGoals(root.root());
        return open.stream()
                .map(Goal::node)
                .map(func)
                .map(s -> s.split(SEPARATOR))
                .map(a -> {
                    ArrayUtils.reverse(a);
                    return a;
                })
                .collect(Collectors.toList());
    }

}
