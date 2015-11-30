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
     * debug function for escaping logicprinter output
     * @param s input String
     * @return String with escaped chars
     */
    public String escape(String s){
        StringBuilder sb = new StringBuilder();
        for (int i=0; i<s.length(); i++)
            switch (s.charAt(i)){
                case '\n': sb.append("\\n"); break;
                case '\t': sb.append("\\t"); break;
                case '\f': sb.append("\\f"); break;
                case '\r': sb.append("\\r"); break;
                case '\b': sb.append("\\b"); break;
                case ' ': sb.append("°"); break;
                default: sb.append(s.charAt(i));
            }
        return sb.toString();
    }
    public String toHTML(String s){
        StringBuilder sb = new StringBuilder();
        sb.append("<p>");
        for (int i=0; i<s.length(); i++)
            switch (s.charAt(i)){
                case '\n': sb.append("</br>"); break;
                case ' ': sb.append("&nbsp;"); break;
                default: sb.append(s.charAt(i));
            }
        return sb.toString();
    }

}
