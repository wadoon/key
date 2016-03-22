package de.uka.ilkd.key.nui.util;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

/**
 * TODO add class comment
 * 
 * @author Victor Schuemmer
 * @version 1.0
 */
public class CssRule {

    private List<String> selectors;
    private HashMap<String, String> propertyValuePairs;

    /**
     * Constructs an empty {@link CssRule}. Notice that a rule without selector
     * is invalid in terms of CSS, so a selector must be given later with
     * {@link #addSelector(String)}.
     * 
     * @param selector
     */
    public CssRule() {
        this(new ArrayList<String>());
    }

    /**
     * Constructs {@link CssRule} with a given selector.
     * 
     * @param selector
     */
    public CssRule(String selector) {
        this(new ArrayList<String>());
        addSelector(selector);
    }

    /**
     * Constructs {@link CssRule} with a list of given selectors.
     * 
     * @param selectors
     *            List of selector Strings
     */
    public CssRule(final List<String> selectors) {
        this.selectors = new ArrayList<String>();
        for (String selector : selectors) {
            addSelector(selector);
        }
        propertyValuePairs = new HashMap<String, String>();
    }

    /**
     * Adds a selector to the rule.
     * 
     * @param selector
     *            the selector String
     * @throws IllegalArgumentException
     *             if the selector contains any space characters (whitespace,
     *             tab, newline)
     */
    public void addSelector(String selector) {
        if (selector.contains(" ") || selector.contains("\n") || selector.contains("\t") || selector.isEmpty())
            throw new IllegalArgumentException("Selector contains spacing or is empty.");
        this.selectors.add(selector);
    }

    /**
     * @return List containing the selectors of this Rule.
     */
    public List<String> getSelectors() {
        return selectors;
    }

    /**
     * Removes the given selector from the rule.
     * 
     * @param selector
     *            the selector String to remove
     * @throws IllegalStateException
     *             if trying to remove the only selector of this rule
     */
    public void removeSelector(String selector) {
        if (selectors.size() == 1)
            throw new IllegalStateException("Cannot remove last selector.");
        selectors.remove(selector);
    }

    /**
     * Adds a pair of property and value to the rule. If the property already
     * exists, the value will be replaced.
     * 
     * @param property
     *            the property String
     * @param value
     *            the value String
     * @throws IllegalArgumentException
     *             if the property contains any space characters (whitespace,
     *             tab, newline) or any argument is an empty String
     */
    public void putPropertyValuePair(String property, String value) {
        if (property.contains(" ") || property.contains("\n") || property.contains("\t") || property.isEmpty())
            throw new IllegalArgumentException("Property contains spacing or is empty.");
        if (value.isEmpty())
            throw new IllegalArgumentException("Value is empty.");
        propertyValuePairs.put(property, value);
    }

    /**
     * @return HashMap containing all property/value pairs
     */
    public HashMap<String, String> getPropertyValuePairs() {
        return propertyValuePairs;
    }

    /**
     * @param property
     *            the property String
     * @return the value String for the given property
     */
    public String getValue(String property) {
        return propertyValuePairs.get(property);
    }

    /**
     * Removes the property/value pair for the given property String
     * 
     * @param property
     */
    public void removeProperty(String property) {
        propertyValuePairs.remove(property);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder(selectorsAsString());
        sb.append(" {\n");
        propertyValuePairs.forEach((k, v) -> {
            sb.append("\t").append(k).append(": ").append(v).append(";\n");
        });
        sb.append("}\n");
        return sb.toString();
    }

    /**
     * TODO add comments
     * @return
     */
    public String selectorsAsString() {
        StringBuilder sb = new StringBuilder();
        sb.append(selectors.get(0));
        for (int i = 1; i < selectors.size(); i++) {
            sb.append(", ").append(selectors.get(i));
        }
        return sb.toString();
    }
}
