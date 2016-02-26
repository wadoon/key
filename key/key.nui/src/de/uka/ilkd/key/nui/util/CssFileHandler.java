package de.uka.ilkd.key.nui.util;

import java.io.File;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.key_project.util.java.IOUtil;

public class CssFileHandler {

    private ArrayList<CssRule> parsedRules;
    private String css;
    private String path;

    private enum State {
        SELECTOR, PROPERTY, VALUE;
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
     * 
     * @throws IOException
     */
    public void writeCssFile(String path) throws IOException {

        String csss = parsedRulestoString();

        FileWriter fw = new FileWriter(path, false);
        fw.write("/*We recommend to only change this file using the KeY CSS Styler */ \n");
        fw.write(csss);
        fw.close();
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
        parsedRules.clear();
        try {
            loadCssFile(path);
        }
        catch (Exception e) {
            System.err.println("Could not read CSS File");
            e.printStackTrace();
        }
    }

    /**
     * writes the CSSFile according to DEFAULT_CSS in NUIConstants
     */
    public void resetDefault() {
        String tmpPath = path;
        parsedRules.clear();
        try {
            loadCssFile(NUIConstants.CSS_RESET_TO_DEFAULT_PATH);
            writeCssFile(tmpPath);
            path = tmpPath;
        }
        catch (Exception e) {
            System.err.println("Could not Reset CSS to Default");
            e.printStackTrace();
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
        boolean inComment = false;

        for (int i = 0; i < css.length() - 1; i++) {
            char c = css.charAt(i);
            if (c == '/' && css.charAt(i + 1) == '*') {
                inComment = true;
                continue;
            }

            if (inComment) {
                if (c == '/' && css.charAt(i - 1) == '*')
                    inComment = false;
                continue;
            }

            switch (state) {
            case SELECTOR: {
                switch (c) {
                case '{': {
                    state = State.PROPERTY;
                    rule.addSelector(selector.trim());
                    selector = "";
                    break;
                }
                case ',': {
                    if (selector.equals(""))
                        System.err
                                .println("Leading comma in selectors ignored.");
                    else
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
                    System.err.println("Semicolon in property ignored.");
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
                case '}': {
                    System.err.println("Bracket in value ignored.");
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
