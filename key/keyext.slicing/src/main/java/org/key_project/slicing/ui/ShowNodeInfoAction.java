package org.key_project.slicing.ui;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.Pair;
import org.key_project.slicing.DependencyTracker;
import org.key_project.slicing.graph.GraphNode;

import javax.swing.*;
import javax.swing.event.HyperlinkEvent;
import java.awt.event.ActionEvent;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;

public class ShowNodeInfoAction extends MainWindowAction {

    private static final long serialVersionUID = -1878750240016534264L;

    private final transient DependencyTracker tracker;

    /**
     * The graph node to use.
     */
    private final transient GraphNode node;

    public ShowNodeInfoAction(MainWindow mw, DependencyTracker tracker, GraphNode node) {
        super(mw);
        setName("Show edges of this dependency graph node");
        this.tracker = tracker;
        this.node = node;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        var graphNodes = new ArrayList<GraphNode>();
        var analysisResults = tracker.getAnalysisResults();
        Function<Pair<Node, GraphNode>, Collection<String>> nodeToTableRow = n -> {
            graphNodes.add(n.second);
            var ruleName = n.first.getAppliedRuleApp().rule().displayName();
            return List.of(
                    Integer.toString(n.first.serialNr()),
                    analysisResults != null && !analysisResults.usefulSteps.contains(n.first) ? ruleName + "*" : ruleName,
                    n.second.toString(false, false));
        };
        var idxFactory = new IndexFactory();

        var headers1 = List.of("Serial Nr.", "Rule name", "Used formula");
        var headers2 = List.of("Serial Nr.", "Rule name", "Produced formula");
        var clickable = new boolean[] { false, false, true };
        var incoming = tracker.getDependencyGraph()
                .incomingGraphEdgesOf(node).map(nodeToTableRow).collect(Collectors.toList());
        var outgoing = tracker.getDependencyGraph()
                .outgoingGraphEdgesOf(node).map(nodeToTableRow).collect(Collectors.toList());
        var html1 = HtmlFactory.generateTable(headers1, clickable, incoming, idxFactory);
        var html2 = HtmlFactory.generateTable(headers2, clickable, outgoing, idxFactory);
        var html = "<h1>Produced by</h1>" + html1 + "<h1>Used by</h1>" + html2;
        new HtmlDialog(SwingUtilities.getWindowAncestor((JComponent) e.getSource()),
                "Dependency graph node info", html, event -> {
            if (event.getEventType() == HyperlinkEvent.EventType.ACTIVATED) {
                System.out.println(event);
                var idx = Integer.parseInt(event.getDescription().substring(1));
                new ShowNodeInfoAction(mainWindow, tracker, graphNodes.get(idx)).actionPerformed(e);
            }
        });
    }
}
