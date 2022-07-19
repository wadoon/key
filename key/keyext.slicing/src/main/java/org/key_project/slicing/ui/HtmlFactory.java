package org.key_project.slicing.ui;

import org.apache.commons.text.StringEscapeUtils;

import java.util.Collection;

public final class HtmlFactory {
    private HtmlFactory() { }

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

    private static String escapeText(String text) {
        return StringEscapeUtils.escapeHtml4(text);
    }
}
