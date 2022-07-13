package org.key_project.slicing.ui;

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
                stats.append(cell);
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
}
