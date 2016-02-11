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
    private String path;

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
     * @param path
     *            path to the css file
     * @throws IOException
     */
    public CssFileHandler(String path) throws IOException {
        this();
        loadCssFile(path);
    }

    /**
     * Loads a css file.
     * 
     * @param path
     *            path to the css file
     * @throws IOException
     */
    public void loadCssFile(String path) throws IOException {
        css = IOUtil.readFrom(new File(path)) + "\n";
        this.path = path;
        parse();
    }

    /**
     * Writes to css file
     * 
     * @param path
     *            path to the css file
     * @throws IOException
     */
    public void writeCssFile(String path) throws IOException {

        File file = new File(path);
        FileOutputStream fop = new FileOutputStream(file);

        css = parsedRulestoString();

        IOUtil.writeTo(fop, css);
    }

    /**
     * 
     * @return a String representation of the parsed and possibly changed Rules.
     *         These are not written into the file.
     */
    public String parsedRulestoString() {
        StringBuilder result = new StringBuilder();
        for (CssRule rule : parsedRules) {
            result.append(rule.toString());
        }
        return result.toString();
    }

    /**
     * writes the currently parsed and possibly rules into the opened CSS file.
     * These changes cannot be reverted
     * 
     * @throws IOException
     */
    public void writeCssFile() throws IOException {
        writeCssFile(path);
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
     * reads the css file again. Usefull to "forget" made changes, that have not
     * been written yet.
     */
    public void reset() {
        try {
            loadCssFile(path);
        }
        catch (Exception e) {
            System.err.println("Could not read CSS File");
        }
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

    /**
     * gets the complete rule from the parsedRule memory, if it contains the
     * given selector
     * 
     * @param selector
     *            the selector to be searched for
     * @return the CssRule which contains the selector
     */
    public CssRule getRule(String selector) {
        for (CssRule rule : parsedRules) {
            if (rule.getSelectors().contains(selector)) {
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
        // String css = removeSpacing(this.css);

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
