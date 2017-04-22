package de.uka.ilkd.key.prototype;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.util.pp.Layouter;
import de.uka.ilkd.key.util.pp.StringBackend;
import javafx.geometry.Orientation;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.Separator;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;
import javafx.scene.text.TextFlow;

import java.io.StringWriter;
import java.util.HashMap;
import java.util.Map;

public class SequentPane extends VBox {
    private Pane antecedent = new TextFlow();
    private Pane succedent = new TextFlow();
    private Map<Pane, Term> map = new HashMap<>();

    public SequentPane(Sequent sequent) {
        Node separator = new Separator(Orientation.HORIZONTAL);
        separator.setId("sequent-separator");
        System.out.println(separator.getStyleClass());

        getChildren().addAll(antecedent, separator, succedent);

        process(antecedent, sequent.antecedent());
        process(succedent, sequent.succedent());
    }

    private void process(Pane pane, Semisequent ss) {
        for (SequentFormula sf : ss.asList()) {
            Term t = sf.formula();
            Pane sfpane = process(t);
            pane.getChildren().add(sfpane);
        }

    }

    private Pane process(Term t) {
        Label operator = new Label(t.op().toString());
        if(t.javaBlock().size()>0) {
            PrettyPrinter pp = new PrettyPrinter(new StringWriter());
            operator.setText("<" + t.javaBlock().toString() + ">");
        }
        TextFlow tpane = new TextFlow();
        GroupHighlighter.install("hl", tpane);

        map.put(tpane, t);

        tpane.setOnMouseClicked((event -> {
            System.out.println(t);
        }));

        if (t.depth() > 0) {
            Label parOpen = new Label("(");
            Label parClose = new Label(")");

            GroupHighlighter.installParens(parOpen, parClose);

            tpane.getChildren().addAll(operator, parOpen);

            int i = 0;
            for (Term sub : t.subs()) {
                tpane.getChildren().add(process(sub));
                if (++i < t.subs().size())
                    tpane.getChildren().add(new Label(", "));
            }
            tpane.getChildren().addAll(parClose);

        }
        else {
            tpane.getChildren().addAll(operator);
        }

        return tpane;
    }
}