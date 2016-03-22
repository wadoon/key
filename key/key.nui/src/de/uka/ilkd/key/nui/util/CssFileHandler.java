package de.uka.ilkd.key.nui.util;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.util.ArrayList;
import java.util.List;
import java.util.prefs.Preferences;

import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.nui.Context;

/**
 * reads and writes CSS files
 * 
 * @author Victor Schuemmer
 * @author Maximilian Li
 * @version 1.0
 */
public class CssFileHandler {

    private ArrayList<CssRule> parsedRules;
    private String css;
    private String path;

    private enum State {
        SELECTOR, PROPERTY, VALUE;
    }

    /**
     * Constructs a {@link CssFileHandler} without a {@link File}. Call
     * {@link #loadCssFile(String)} to add the file afterwards.
     * 
     * @throws IOException
     */
    public CssFileHandler() throws IOException {
        css = "";
        parsedRules = new ArrayList<CssRule>();
    }

    /**
     * Constructs a {@link CssFileHandler} with a {@link File}.
     * 
     * @param path
     *            path to the file
     * @throws IOException
     */
    public CssFileHandler(String path) throws IOException {
        this();
        loadCssFile(path);
    }

    /**
     * @return path to the loaded {@link File}
     */
    public String getPath() {
        return path;
    }

    /**
     * Sets a path to a {@link File}.
     * 
     * @param path
     *            path to the file
     */
    public void setPath(String path) {
        this.path = path;
        Preferences prefs = Preferences.userNodeForPackage(Context.class);
        prefs.put(NUIConstants.PREFERENCES_CSSPATH_KEY, path);
    }

    /**
     * Loads a CSS {@link File}.
     * 
     * @param path
     *            path to the CSS file
     * @throws IOException
     */
    public void loadCssFile(String path) throws IOException {
        File file = new File(path);
        if (file.exists() && !file.isDirectory()) {
            css = IOUtil.readFrom(new File(path)) + "\n";
            setPath(path);
        }
        parse();
    }

    /**
     * Writes to CSS {@link File}.
     * 
     * @param path
     *            path to the CSS file
     * 
     * @throws IOException
     */
    public void writeCssFile(String path) throws IOException {
        css = parsedRulestoString();

        if (path.isEmpty()) {
            return;
        }

        File file = new File(path);
        Writer w = new OutputStreamWriter(new FileOutputStream(file), "UTF-8");
        try {
            w.write("/*We recommend to only change this file using the KeY CSS Styler */ \n");
            w.write(css);
        }
        catch (final IOException e) {
            e.printStackTrace();
        }
        finally {
            w.close();
        }
    }

    /**
     * @return A String representation of the parsed and possibly changed rules.
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
     * Writes the currently parsed and possible rules into the opened CSS file.
     * These changes cannot be reverted!
     * 
     * @throws IOException
     */
    public void writeCssFile() throws IOException {
        writeCssFile(path);
    }

    /**
     * Adds a rule to the CSS. Does NOT automatically add it to parsedRules.
     * 
     * @param rule
     */
    public void addCssRule(CssRule rule) {
        css += rule.toString();
    }

    /**
     * Reads the CSS file again. Useful to "forget" made changes, that have not
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
     * Writes the CSS file according to DEFAULT_CSS in NUIConstants
     */
    public void resetDefault() {
        String tmpPath = path;
        parsedRules.clear();
        try {
            loadCssFile(NUIConstants.DEFAULT_CSS_PATH);
            writeCssFile(tmpPath);
            setPath(tmpPath);
        }
        catch (Exception e) {
            System.err.println("Could not Reset CSS to Default");
            e.printStackTrace();
        }
    }

    /**
     * @return the CSS content string
     */
    public String getCss() {
        return css;
    }

    /**
     * Returns a List of CssRules parsed from the CSS file. List will be empty
     * if no file was loaded.
     * 
     * @return List of CssRules
     */
    public List<CssRule> getParsedRules() {
        return parsedRules;
    }

    /**
     * Gets the complete rule from the parsedRule memory if it contains the
     * given selector.
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
     * Parses the loaded CSS and returns the rules.
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
                        System.err.println("Leading comma in selectors ignored.");
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
