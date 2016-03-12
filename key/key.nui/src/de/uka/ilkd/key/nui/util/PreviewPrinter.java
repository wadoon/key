/**
 * 
 */
package de.uka.ilkd.key.nui.util;

/**
 * Provides a dummy text that can be printed with CSS as a preview.
 * 
 * @author Maximilian Li
 */
public class PreviewPrinter {
    private final static String PREVIEW_TEXT = "This is a preview text\n"
            + "It shows you how elemts in this class will be styled. \n"
            + "Use the controls to change certain settings. \n"
            + "All changes can be reverted by the 'Reset to Default' menu entry.";

    public static String printPreview(String css, CssRule rule) {
        StringBuilder sb = new StringBuilder();
        String selector = rule.selectorsAsString();
        sb.append("<head>");

        sb.append("<style>");
        sb.append(css);
        sb.append("</style>");

        sb.append("</head><body>");
        sb.append("<pre>");

        sb.append(NUIConstants.OPEN_TAG_BEGIN);
        sb.append(selector.substring(1, selector.length()));
        sb.append(NUIConstants.OPEN_TAG_END);

        sb.append(PREVIEW_TEXT);

        sb.append(NUIConstants.CLOSING_TAG);
        sb.append("</pre></body>");

        return sb.toString();
    }

}
