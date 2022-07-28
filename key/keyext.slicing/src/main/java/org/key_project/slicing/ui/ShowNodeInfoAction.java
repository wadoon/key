package org.key_project.slicing.ui;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.Triple;
import org.key_project.slicing.DependencyTracker;
import org.key_project.slicing.graph.AnnotatedEdge;
import org.key_project.slicing.graph.GraphNode;

import javax.swing.*;
import javax.swing.event.HyperlinkEvent;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;

public class ShowNodeInfoAction extends MainWindowAction {

    private static final long serialVersionUID = -1878750240016534264L;

    private final transient DependencyTracker tracker;

    /**
     * The graph node to show information on.
     */
    private final transient GraphNode node;

    public ShowNodeInfoAction(MainWindow mw, DependencyTracker tracker, GraphNode node) {
        super(mw);
        setName("Show dependency graph info");
        this.tracker = tracker;
        this.node = node;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        showDialog(SwingUtilities.getWindowAncestor((JComponent) e.getSource()));
    }

    private void showDialog(Window parentWindow) {
        var graphNodes = new ArrayList<GraphNode>();
        var analysisResults = tracker.getAnalysisResults();
        Function<Triple<Node, GraphNode, AnnotatedEdge>, Collection<String>> nodeToTableRow = n -> {
            graphNodes.add(n.second);
            var ruleName = n.first.getAppliedRuleApp().rule().displayName();
            return List.of(
                    Integer.toString(n.first.serialNr()),
                    analysisResults != null && !analysisResults.usefulSteps.contains(n.first) ? "<strike>" + ruleName + "</strike>" : ruleName,
                    n.third.consumesInput ? "yes" : "no",
                    n.second.toString(false, false));
        };
        var idxFactory = new IndexFactory();

        var headers1 = List.of("Serial Nr.", "Rule name", "Consumed", "Used formula");
        var headers2 = List.of("Serial Nr.", "Rule name", "Consumed", "Produced formula");
        var clickable = new boolean[] { false, false, false, true };
        var incoming = tracker.getDependencyGraph()
                .incomingGraphEdgesOf(node).map(nodeToTableRow).collect(Collectors.toList());
        var outgoing = tracker.getDependencyGraph()
                .outgoingGraphEdgesOf(node).map(nodeToTableRow).collect(Collectors.toList());
        var html1 = HtmlFactory.generateTable(headers1, clickable, Optional.empty(), incoming, idxFactory);
        var html2 = HtmlFactory.generateTable(headers2, clickable, Optional.empty(), outgoing, idxFactory);
        var useful = analysisResults != null ? tracker.getDependencyGraph().outgoingGraphEdgesOf(node).filter(t -> analysisResults.usefulSteps.contains(t.first)).count() : -1;
        var extraInfo = useful != -1 ? "<h2>" + useful + " useful rule apps</h2>" : "";
        var html = "<h1>Produced by</h1>" + html1
                + "<h1>This node</h1>" + "<p>" + node.toString(false, false) + "</p>"
                + "<h1>Used by</h1>"
                + extraInfo
                + html2
                + "<p>strikethrough rule name = useless rule app</p>";
        new HtmlDialog(parentWindow,
                "Dependency graph node info", html, event -> {
            if (event.getEventType() == HyperlinkEvent.EventType.ACTIVATED) {
                var idx = Integer.parseInt(event.getDescription().substring(1));
                new ShowNodeInfoAction(mainWindow, tracker, graphNodes.get(idx))
                        .showDialog(SwingUtilities.getWindowAncestor((JComponent) event.getSource()));
            }
        });
    }
}
