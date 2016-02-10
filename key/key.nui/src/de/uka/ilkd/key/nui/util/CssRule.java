package de.uka.ilkd.key.nui.util;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

/**
 * 
 * @author Victor Schuemmer
 */
public class CssRule {

    private List<String> selectors;
    private HashMap<String, String> propertyValuePairs;
    
    /**
     * Constructs an empty CssRule.
     */
    public CssRule() {
        this(new ArrayList<String>());
    }
    
    /**
     * Constructs CssRule with given selector.
     * @param selector
     */
    public CssRule(String selector) {
        this(new ArrayList<String>());
        addSelector(selector);
    }
    
    /**
     * Constructs CssRule with given selectors.
     * @param selectors List of selector Strings
     */
    public CssRule(final List<String> selectors) {
        this.selectors = selectors;
        propertyValuePairs = new HashMap<String, String>();
    }
    
    /**
     * Adds a selector to the rule.
     * @param selector the selector String
     */
    public void addSelector(String selector) {
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
     * @param selector the selector String to remove
     */
    public void removeSelector(String selector) {
        selectors.remove(selector);
    }
    
    /**
     * Adds a pair of property and value to the rule.
     * If the property already exists, the value will be replaced.
     * @param property the property String
     * @param value the value String
     */
    public void putPropertyValuePair(String property, String value) {
        propertyValuePairs.put(property, value);
    }
    
    /**
     * @return HashMap containing all property/value pairs
     */
    public HashMap<String, String> getPropertyValuePairs() {
        return propertyValuePairs;
    }
    
    /**
     * 
     * @param property the property String
     * @return the value String for the given property
     */
    public String getValue(String property) {
        return propertyValuePairs.get(property);
    }
    
    /**
     * Removes the property/value pair for the given property String
     * @param property
     */
    public void removeProperty(String property) {
        propertyValuePairs.remove(property);
    }
    
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(selectors.get(0));
        for (int i = 1; i < selectors.size(); i++) {
            sb.append(", ").append(selectors.get(i));
        }
        sb.append(" {\n");
        propertyValuePairs.forEach((k,v) -> {sb.append("\t").append(k).append(": ").append(v).append("\n");});
        sb.append("}\n");
        return sb.toString();
    }    
}
