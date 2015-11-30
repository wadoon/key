/**
 * 
 */
package de.uka.ilkd.key.nui.util;

/**
 * @author Maximilian Li
 *
 */
public class SequentPrinter {

    /**
     * 
     */
    public SequentPrinter() {
        // TODO Auto-generated constructor stub
    }

    /**
     * debug function for escaping LogicPrinter output
     * 
     * @param s
     *            input String
     * @return String with escaped chars
     */
    public String escape(String s) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < s.length(); i++)
            switch (s.charAt(i)) {
            case '\n':
                sb.append("\\n");
                break;
            case '\t':
                sb.append("\\t");
                break;
            case '\f':
                sb.append("\\f");
                break;
            case '\r':
                sb.append("\\r");
                break;
            case '\b':
                sb.append("\\b");
                break;
            case ' ':
                sb.append("°");
                break;
            default:
                sb.append(s.charAt(i));
            }
        return sb.toString();
    }

    /**
     * prints a Sequent as HTML with basic markup
     * 
     * @param s
     *            input SequentString from LogicPrinter
     * @return HTML Text with default style
     */
    public String printSequent(String s) {
        String result = toHTML(s);
        result = colorString(result, "\\\\forall", "red", true);
        result = styleString(result, "->", "black", "yellow", "bold");

        return result;
    }

    /**
     * converts the input String to HTML tagged text
     * 
     * @param s
     *            input string
     * @return String with HTML tags
     */
    public String toHTML(String s) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < s.length(); i++)
            switch (s.charAt(i)) {
            case '\n':
                sb.append("</br>");
                break;
            case ' ':
                sb.append("&nbsp;");
                break;
            default:
                sb.append(s.charAt(i));
            }
        return sb.toString();
    }

    /**
     * colors all the appearances of the given substring
     * 
     * @param s input string
     * @param searchString string to be searched for
     * @param fontColor color for the results
     * @return string with HTML style tags applied
     */
    public String colorString(String s, String searchString, String fontColor) {
        return styleString(s, searchString, fontColor, "white", "normal");
    }
    /**
     * colors all the appearances of the given substring
     * 
     * @param s input string
     * @param searchString string to be searched for
     * @param fontColor color for the results
     * @param boldness true if results should be bold
     * @return string with HTML style tags applied
     */
    public String colorString(String s, String searchString, String fontColor,
            boolean boldness) {
        if (boldness) {
            return styleString(s, searchString, fontColor, "white", "bold");
        }
        else {
            return styleString(s, searchString, fontColor, "white", "normal");
        }
    }
    /**
     * colors the substring from start to end
     * @param s the input string
     * @param start startIndex of the substring
     * @param length length of the substring
     * @param fontColor the color
     * @return string with HTML style tags applied
     */
    public String colorString(String s, int start, int length,
            String fontColor) {
        return styleString(s, start, length, fontColor, "white", "normal");
    }
    /**
     * colors the substring from start to end
     * @param s the input string
     * @param start startIndex of the substring
     * @param length length of the substring
     * @param fontColor the color
     * @param boldness true if results should be bold
     * @return string with HTML style tags applied
     */
    public String colorString(String s, int start, int length, String fontColor,
            Boolean boldness) {
        if (boldness) {
            return styleString(s, start, length, fontColor, "white", "bold");
        }
        else {
            return styleString(s, start, length, fontColor, "white", "normal");
        }

    }
    /**
     * highlights all the appearances of given substring
     * @param s the input string
     * @param searchString the substring to be searched for
     * @param backgroundColor the highlighting color
     * @return string with HTML style tags applied
     */
    public String highlightString(String s, String searchString,
            String backgroundColor) {
        return styleString(s, searchString, "black", backgroundColor, "normal");
    }
    /**
     * highlights all the appearances of given substring
     * @param s the input string
     * @param searchString the substring to be searched for
     * @param backgroundColor the highlighting color
     * @param boldness true if results should be bold
     * @return string with HTML style tags applied
     */
    public String highlightString(String s, String searchString,
            String backgroundColor, boolean boldness) {
        if (boldness) {
            return styleString(s, searchString, "black", backgroundColor,
                    "bold");
        }
        else {
            return styleString(s, searchString, "black", backgroundColor,
                    "normal");
        }
    }
    /**
     * highlights the substring from start to end
     * @param s the input string
     * @param start startIndex of the substring
     * @param length length of the substring
     * @param backgroundColor the highlighting color
     * @return string with HTML style tags applied
     */
    public String highlightString(String s, int start, int length,
            String backgroundColor) {
        return styleString(s, start, length, "black", backgroundColor,
                "normal");
    }
    /**
     * highlights the substring from start to end
     * @param s the input string
     * @param start startIndex of the substring
     * @param length length of the substring
     * @param backgroundColor the highlighting color
     * @param boldness true if results should be bold
     * @return string with HTML style tags applied
     */
    public String highlightString(String s, int start, int length,
            String backgroundColor, boolean boldness) {
        if (boldness) {
            return styleString(s, start, length, "black", backgroundColor,
                    "bold");
        }
        else {
            return styleString(s, start, length, "black", backgroundColor,
                    "normal");
        }

    }
    /**
     * styles all the appearances of given substring
     * @param s the input string
     * @param searchString the substring to be searched for
     * @param fontColor the color
     * @param backgroundColor the highlighting color
     * @param fontWeight "bold" for bold, else "normal
     * @return string with HTML style tags applied
     */
    public String styleString(String s, String searchString, String fontColor,
            String backgroundColor, String fontWeight) {

        return s.replaceAll(searchString,
                "<span style=\"color:" + fontColor + ";background-color:"
                        + backgroundColor + ";font-weight:" + fontWeight + "\">"
                        + searchString + "</span>");
    }
    /**
     * highlights the substring from start to end
     * @param s the input string
     * @param start startIndex of the substring
     * @param length length of the substring
     * @param fontColor the color
     * @param backgroundColor the highlighting color
     * @param fontWeight "bold" for bold, else "normal
     * @return string with HTML style tags applied
     */
    public String styleString(String s, int start, int length, String fontColor,
            String backgroundColor, String fontWeight) {
        StringBuilder sb = new StringBuilder(s);
        sb.insert(start + length, "</span>");
        sb.insert(start,
                "<span style=\"color:" + fontColor + ";background-color:"
                        + backgroundColor + ";font-weight:" + fontWeight
                        + "\">");
        return sb.toString();
    }

}
