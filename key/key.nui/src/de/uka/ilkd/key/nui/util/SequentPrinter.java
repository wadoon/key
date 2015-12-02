/**
 * 
 */
package de.uka.ilkd.key.nui.util;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashMap;

/**
 * @author Maximilian Li
 * @author Victor Schuemmer
 */
public class SequentPrinter {
    private String css;
    private HashMap<String, String> dictionaryMap = new HashMap<String, String>();
    private HashMap<String, String> regexMap = new HashMap<String, String>();
    private String freeTextSearch = "";

    /**
     * Constructor for the SequentPrinter
     * 
     * @param cssPath
     *            Path to the CSS file for Styling
     */
    public SequentPrinter(String cssPath, String classPath) {
        // TODO Auto-generated constructor stub
        try {
            readCSS(cssPath);
        }
        catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        try {
            readIni(classPath);
        }
        catch (Exception e) {
            e.printStackTrace();
        }
    }

    public void setFreeTextSearch(String searchString) {
        freeTextSearch = searchString;
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
            case '\\':
                sb.append("\\\\");
                break;
            case '(':
                sb.append("\\(");
                break;
            case ')':
                sb.append("\\)");
                break;
            case '{':
                sb.append("\\{");
                break;
            case '}':
                sb.append("\\}");
                break;
            default:
                sb.append(s.charAt(i));
            }
        return sb.toString();
    }

    public void infuseCSS(String additionalCss) {
        css += additionalCss;
    }

    /**
     * prints a Sequent as HTML with basic markup
     * 
     * @param s
     *            input SequentString from LogicPrinter
     * @return HTML Text with default style
     */
    public String printSequent(String s) {
        String result = highlightString(s, freeTextSearch);
        result = toHTML(result);
        for (String classString : dictionaryMap.keySet()) {
            result = styleHTMLEscaped(result, dictionaryMap.get(classString),
                    classString);
        }
        // result = highlightString(result, "->");
        //result = highlightString(result, freeTextSearch);
        return result;
    }

    /**
     * sets the CSS information
     * 
     * @param fileName
     *            path to the CSS file
     * @throws IOException
     */
    public void readCSS(String fileName) throws IOException {
        BufferedReader br = new BufferedReader(new FileReader(fileName));
        try {
            StringBuilder sb = new StringBuilder();
            String line = br.readLine();

            while (line != null) {
                sb.append(line);
                sb.append("\n");
                line = br.readLine();
            }
            this.css = sb.toString();
        }
        finally {
            br.close();
        }
    }

    /**
     * reads the .ini file and builds the Dictionary and RegEx Maps
     * 
     * @param fileName
     *            path to the .ini file
     * @throws IOException
     */
    public void readIni(String fileName) throws IOException {
        BufferedReader br = new BufferedReader(new FileReader(fileName));
        try {
            String line = br.readLine();
            String[] lineParts;
            while (line != null) {
                lineParts = line.split(" ");
                switch (line.charAt(0)) {
                case '/':
                    break;
                case 'd':
                    dictionaryMap.put(lineParts[1], lineParts[2]);
                    break;
                case 'r':
                    regexMap.put(lineParts[1], lineParts[2]);
                    break;
                default:
                    break;
                }

                line = br.readLine();
            }
        }
        finally {
            br.close();
        }
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
        sb.append("<style>");
        sb.append(css);
        sb.append("</style>");
        /*
         * for (int i = 0; i < s.length(); i++) switch (s.charAt(i)) { case
         * '\n': sb.append("</br>"); break; case ' ': sb.append("&nbsp;");
         * break; default: sb.append(s.charAt(i)); }
         */
        sb.append("<pre>");
        sb.append(s);
        sb.append("</pre>");
        return sb.toString();
    }

    /**
     * Styles all the appearances of the given substring with given CSS
     * Styleclass
     * 
     * @param s
     *            input string
     * @param searchString
     *            string to be styled
     * @param styleClass
     *            the CSS StyleClass
     * @return string with HTML style tags applied
     */
    public String styleHTML(String s, String searchString, String styleClass) {
        if (!searchString.isEmpty())
            return styleHTMLEscaped(s, escape(searchString), styleClass);
        else
            return s;
    }

    private String styleHTMLEscaped(String s, String searchString,
            String styleClass) {
        if (!searchString.isEmpty())
            return s.replaceAll(searchString, "<span class=\"" + styleClass
                    + "\">" + searchString + "</span>");
        else
            return s;
    }

    /**
     * styles the substring from start to end
     * 
     * @param s
     *            the input string
     * @param start
     *            startIndex of the substring
     * @param length
     *            length of the substring
     * @param styleClass
     *            the CSS style which is to be applied
     * @return string with HTML style tags applied
     */
    public String styleHTML(String s, int start, int length,
            String styleClass) {
        StringBuilder sb = new StringBuilder(s);
        sb.insert(start + length, "</span>");
        sb.insert(start, "<span class=\"" + styleClass + "\">");
        return sb.toString();
    }

    /**
     * highlights all the appearances of the given substring according to CSS
     * 
     * @param s
     *            input string
     * @param searchString
     *            string to be highlighted
     * @return string with HTML style tags applied
     */
    public String highlightString(String s, String searchString) {
        return styleHTML(s, searchString, "highlighted");
    }

    /**
     * highlights the substring from start to end
     * 
     * @param s
     *            the input string
     * @param start
     *            startIndex of the substring
     * @param length
     *            length of the substring
     * @return string with HTML style tags applied
     */
    public String highlightString(String s, int start, int length) {
        return styleHTML(s, start, length, "highlighted");
    }

    /**
     * colors all the appearances of the given substring
     * 
     * @param s
     *            input string
     * @param searchString
     *            string to be searched for
     * @param fontColor
     *            color for the results
     * @return string with HTML style tags applied
     */
    public String colorString(String s, String searchString, String fontColor) {
        return styleString(s, searchString, fontColor, "white", "normal");
    }

    /**
     * colors all the appearances of the given substring
     * 
     * @param s
     *            input string
     * @param searchString
     *            string to be searched for
     * @param fontColor
     *            color for the results
     * @param boldness
     *            true if results should be bold
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
     * 
     * @param s
     *            the input string
     * @param start
     *            startIndex of the substring
     * @param length
     *            length of the substring
     * @param fontColor
     *            the color
     * @return string with HTML style tags applied
     */
    public String colorString(String s, int start, int length,
            String fontColor) {
        return styleString(s, start, length, fontColor, "white", "normal");
    }

    /**
     * colors the substring from start to end
     * 
     * @param s
     *            the input string
     * @param start
     *            startIndex of the substring
     * @param length
     *            length of the substring
     * @param fontColor
     *            the color
     * @param boldness
     *            true if results should be bold
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
     * 
     * @param s
     *            the input string
     * @param searchString
     *            the substring to be searched for
     * @param backgroundColor
     *            the highlighting color
     * @return string with HTML style tags applied
     */
    public String highlightStringCustom(String s, String searchString,
            String backgroundColor) {
        return styleString(s, searchString, "black", backgroundColor, "normal");
    }

    /**
     * highlights all the appearances of given substring
     * 
     * @param s
     *            the input string
     * @param searchString
     *            the substring to be searched for
     * @param backgroundColor
     *            the highlighting color
     * @param boldness
     *            true if results should be bold
     * @return string with HTML style tags applied
     */
    public String highlightStringCustom(String s, String searchString,
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
     * 
     * @param s
     *            the input string
     * @param start
     *            startIndex of the substring
     * @param length
     *            length of the substring
     * @param backgroundColor
     *            the highlighting color
     * @return string with HTML style tags applied
     */
    public String highlightStringCustom(String s, int start, int length,
            String backgroundColor) {
        return styleString(s, start, length, "black", backgroundColor,
                "normal");
    }

    /**
     * highlights the substring from start to end
     * 
     * @param s
     *            the input string
     * @param start
     *            startIndex of the substring
     * @param length
     *            length of the substring
     * @param backgroundColor
     *            the highlighting color
     * @param boldness
     *            true if results should be bold
     * @return string with HTML style tags applied
     */
    public String highlightStringCustom(String s, int start, int length,
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
     * 
     * @param s
     *            the input string
     * @param searchString
     *            the substring to be searched for
     * @param fontColor
     *            the color
     * @param backgroundColor
     *            the highlighting color
     * @param fontWeight
     *            "bold" for bold, else "normal
     * @return string with HTML style tags applied
     */
    public String styleString(String s, String searchString, String fontColor,
            String backgroundColor, String fontWeight) {
        if (!searchString.isEmpty())
            return s.replaceAll(escape(searchString),
                    "<span style=\"color:" + fontColor + ";background-color:"
                            + backgroundColor + ";font-weight:" + fontWeight
                            + "\">" + searchString + "</span>");
        else
            return s;
    }

    /**
     * highlights the substring from start to end
     * 
     * @param s
     *            the input string
     * @param start
     *            startIndex of the substring
     * @param length
     *            length of the substring
     * @param fontColor
     *            the color
     * @param backgroundColor
     *            the highlighting color
     * @param fontWeight
     *            "bold" for bold, else "normal
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
