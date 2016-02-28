/**
 * 
 */
package de.uka.ilkd.key.nui.util;

/**
 * @author Maximilian Li
 *
 */
public class PreviewPrinter {
    private final static String PREVIEW_TEXT = "This is a preview:\n"
            + "Lorem ipsum sit doloret...";

    /**
     * 
     */
    public PreviewPrinter() {

    }
    
    public String printPreview(String css, CssRule rule){
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
