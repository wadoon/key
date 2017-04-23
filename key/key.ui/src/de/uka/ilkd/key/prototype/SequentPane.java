package de.uka.ilkd.key.prototype;

import com.sun.javafx.scene.control.skin.TextAreaSkin;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.*;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.util.pp.Backend;
import javafx.geometry.Orientation;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.Separator;
import javafx.scene.control.TextArea;
import javafx.scene.control.TextField;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.Border;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;
import javafx.scene.text.Font;
import javafx.scene.text.TextFlow;

import java.io.StringWriter;
import java.util.HashMap;
import java.util.Map;

public class SequentPane extends BorderPane {
    private final LogicPrinter.PosTableStringBackend backend;
    private final Sequent sequent;
    private Pane antecedent = new TextFlow();
    private Pane succedent = new TextFlow();
    private Map<Pane, Term> map = new HashMap<>();
    private NotationInfo notation;

    private TextArea tf = new TextArea();

    private LogicPrinter lp;
    private IdentitySequentPrintFilter filter;

    public SequentPane(Sequent sequent, Services services) {
        this.sequent = sequent;
        filter = new IdentitySequentPrintFilter(this.sequent);

        Node separator = new Separator(Orientation.HORIZONTAL);
        separator.setId("sequent-separator");
        System.out.println(separator.getStyleClass());

        //getChildren().addAll(antecedent, separator, succedent);

        ProgramPrinter prgPrinter = new ProgramPrinter(new StringWriter());
        this.backend = new LogicPrinter.PosTableStringBackend(80);

        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUseUnicode(true);
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUsePretty(true);
        NotationInfo.DEFAULT_UNICODE_ENABLED = true;
        NotationInfo.DEFAULT_PRETTY_SYNTAX = true;

        notation = new NotationInfo();
        notation.refresh(services, true, true);

        System.out.println(notation.isUnicodeEnabled());
        System.out.println(notation.isPrettySyntax());

        lp = new LogicPrinter(prgPrinter, notation, backend, services, false);

        lp.printSequent(sequent);

        System.out.println(backend.getString());
        setCenter(tf);

        tf.setPrefColumnCount(80);
        tf.setFont(new Font("Fira Code", 24));
        tf.setEditable(false);

        tf.setText(backend.getString());

        tf.setOnMouseMoved(this::hightlight);

        /*
        process(antecedent, sequent.antecedent());
        process(succedent, sequent.succedent());
        */
    }

    private void hightlight(MouseEvent mouseEvent) {
        double x = mouseEvent.getX();
        double y = mouseEvent.getY();

        TextAreaSkin skin = (TextAreaSkin) tf.getSkin();
        int insertionPoint = skin.getInsertionPoint(x, y);

        PosInSequent pis = backend.getInitialPositionTable().getPosInSequent(insertionPoint, filter);
        if (pis != null) {
            System.out.println(pis);
            Range r = backend.getPositionTable().rangeForIndex(insertionPoint, tf.getLength());

            tf.selectRange(r.start(), r.end());
        } else {
            tf.selectRange(0,0);
        }

        mouseEvent.consume();
    }

    private Node process(LogicPrinter.PosTableStringBackend backend) {
        String string = backend.getString();
        System.out.println(string);
        System.out.println(backend.getPositionTable());
        return process("> ", string, backend.getPositionTable());
    }

    private Node process(String indent, String text, PositionTable table) {
        TextFlow flow = new TextFlow();

        for (int i = 0; i < table.getRows(); i++) {
            System.out.println(table.getStartPos()[i] + ":" + table.getEndPos()[i] + " > " + text.length());

            final String substring = text.substring(table.getStartPos()[i], table.getEndPos()[i]);
            System.out.println(indent + ": " + substring);
            System.out.println();

            //flow.getChildren().add();
            process(indent + "\t", substring, table.getChild(i));
        }

        return flow;
    }

    private void process(Pane pane, Semisequent ss) {
        /*for (SequentFormula sf : ss.asList()) {
            Term t = sf.formula();
            Pane sfpane = process(t);
            pane.getChildren().add(sfpane);
        }*/
    }

    private Pane process(Term t) {
        Label operator = new Label(t.op().toString());

        if (t.javaBlock().size() > 0) {
            //LogicPrinter pp = new LogicPrinter(new StringWriter());
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