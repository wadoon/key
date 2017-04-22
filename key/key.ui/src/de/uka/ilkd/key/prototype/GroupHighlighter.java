package de.uka.ilkd.key.prototype;

import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.input.MouseEvent;

import java.util.Arrays;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (18.04.17)
 */
public class GroupHighlighter {
    private final String styleClass;
    private final List<Node> nodes;

    GroupHighlighter(String clazzname, List<Node> ts) {
        nodes = ts;
        for (Node n : ts) {
            n.setOnMouseEntered(this::enter);
            n.setOnMouseExited(this::exit);
        }
        styleClass = clazzname;
    }

    private void exit(MouseEvent mouseEvent) {
        for (Node n : nodes)
            n.getStyleClass().removeAll(styleClass);
    }

    private void enter(MouseEvent mouseEvent) {
        for (Node n : nodes)
            n.getStyleClass().add(styleClass);
    }

    public static void installParens(Label left, Label right) {
        install("paren-hl", left, right);
    }

    public static void install(String clazzname, Node... nodes) {
        new GroupHighlighter(clazzname, Arrays.asList(nodes));
    }
}
