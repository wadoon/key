package org.key_project.slicing.ui;

import org.apache.commons.text.StringEscapeUtils;

import javax.swing.*;
import java.util.Collection;

public final class HtmlFactory {
    private HtmlFactory() { }

    /**
     * @param columnNames
     * @param clickable
     * @param rows
     * @param indexFactory only required if any entry in clickable is true
     * @return
     */
    public static String generateTable(
            Collection<String> columnNames,
            boolean[] clickable,
            Collection<Collection<String>> rows,
            IndexFactory indexFactory
    ) {
        if (columnNames.size() != clickable.length) {
            throw new IllegalArgumentException();
        }

        StringBuilder stats = new StringBuilder("<table><thead>");
        for (var a : columnNames) {
            stats.append("<td>").append(a).append("</td>");
        }
        stats.append("</thead><tbody>");

        for (var row : rows) {
            stats.append("<tr>");
            var i = 0;
            for (var cell : row) {
                stats.append("<td>");
                if (clickable[i]) {
                    stats.append("<a href='#");
                    stats.append(indexFactory.nextIndex());
                    stats.append("'>");
                }
                if (cell.startsWith("<")) {
                    stats.append(cell);
                } else {
                    stats.append(escapeText(cell));
                }
                if (clickable[i]) {
                    stats.append("</a>");
                }
                stats.append("</td>");
                i++;
            }
            stats.append("</tr>");
        }

        stats.append("</tbody></table>");
        return stats.toString();
    }

    public static JComponent createComponent(String html) {
        JEditorPane htmlContent = new JEditorPane("text/html", html);
        htmlContent.setEditable(false);
        htmlContent.setBorder(BorderFactory.createEmptyBorder());
        htmlContent.setCaretPosition(0);
        return htmlContent;
    }

    private static String escapeText(String text) {
        return StringEscapeUtils.escapeHtml4(text);
    }
}
