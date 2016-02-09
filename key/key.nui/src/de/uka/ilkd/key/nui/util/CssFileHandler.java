package de.uka.ilkd.key.nui.util;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;

import org.key_project.util.java.IOUtil;

public class CssFileHandler {

    private ArrayList<CssRule> parsedRules;
    private String css;

    private enum State {
        COMMENT, SELECTOR, PROPERTY, VALUE;
    }

    /**
     * Constructs a CssFileHandler without file. Call loadCssFile to add the
     * file afterwards.
     */
    public CssFileHandler() {
        css = "";
        parsedRules = new ArrayList<CssRule>();
    }

    /**
     * Constructs a CssFileHandler.
     * 
     * @param url
     *            path to the css file
     * @throws IOException
     */
    public CssFileHandler(URL url) throws IOException {
        this();
        loadCssFile(url);
    }

    public CssFileHandler(File file) throws IOException {
        this();
        loadCssFile(file);
    }

    /**
     * Loads a css file.
     * 
     * @param url
     *            path to the css file
     * @throws IOException
     */
    public void loadCssFile(URL url) throws IOException {
        css = IOUtil.readFrom(url) + "\n";
        parse();
    }

    public void loadCssFile(File file) throws IOException {
        css = IOUtil.readFrom(file) + "\n";
        parse();
    }

    /**
     * Writes to css file
     * 
     * @param url
     *            path to the css file
     * @throws IOException
     */
    public void writeCssFile(URL url) throws IOException {

        File file = new File(IOUtil.toURI(url));
        FileOutputStream fop = new FileOutputStream(file);
        IOUtil.writeTo(fop, css);
    }

    /**
     * Adds a rule to the css. Does NOT automatically add it to parsedRules.
     * 
     * @param rule
     */
    public void addCssRule(CssRule rule) {
        css += rule.toString();
    }

    /**
     * @return the css content string
     */
    public String getCss() {
        return css;
    }

    /**
     * Returns a List of CssRules parsed from the css file. List will be empty
     * if no file was loaded.
     * 
     * @return List of CssRules
     */
    public List<CssRule> getParsedRules() {
        return parsedRules;
    }
    
    public CssRule getRule(String selector){
        for(CssRule rule : parsedRules){
            if (rule.getSelectors().contains(selector)){
                return rule;
            }
        }
        return null;
    }

    private String removeSpacing(String str) {
        return str.replace("\n", "").replace("\r", "").replace("\t", "")
                .replace(" ", "");
    }

    /**
     * Parses the loaded css and returns the rules.
     * 
     * @return List of CssRules
     */
    private void parse() {
        CssRule rule = new CssRule();
        String selector = "";
        String property = "";
        String value = "";
        State state = State.SELECTOR;
        //String css = removeSpacing(this.css);
        
        for (int i = 0; i < css.length() - 1; i++) {
            char c = css.charAt(i);
            if (c == '/' && css.charAt(i + 1) == '*') {
                // state = State.COMMENT;
            }

            switch (state) {
            case COMMENT: {
                // TODO implement comment handle
                break;
            }
            case SELECTOR: {
                switch (c) {
                case '{': {
                    state = State.PROPERTY;
                    rule.addSelector(selector.trim());
                    selector = "";
                    break;
                }
                case ',': {
                    // TODO catch leading comma
                    // if (selector.equals(""))
                    rule.addSelector(selector.trim());
                    selector = "";
                }
                default:
                    selector += c;
                }
                break;
            }
            case PROPERTY: {
                switch (c) {
                case ':': {
                    state = State.VALUE;
                    break;
                }
                case ';': {
                    // TODO catch
                    break;
                }
                case '}': {

                    parsedRules.add(rule);
                    rule = new CssRule();
                    state = State.SELECTOR;
                    break;
                }
                default:
                    property += c;
                }
                break;
            }
            case VALUE: {
                switch (c) {
                case ';': {
                    rule.putPropertyValuePair(property.trim(), value.trim());
                    property = "";
                    value = "";
                    state = State.PROPERTY;
                    break;
                }
                case ',': {
                    // TODO catch
                    break;
                }
                case '}': {
                    // TODO catch
                    break;
                }
                default:
                    value += c;
                }
                break;
            }
            }
        }
    }
}
