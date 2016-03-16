package de.uka.ilkd.key.nui.test;

import static org.junit.Assert.*;

import java.util.ArrayList;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import de.uka.ilkd.key.nui.util.CssRule;

public class CssRuleTest {
    
    @Test
    public void testEmptyRule() {
        CssRule rule = new CssRule();
        assertTrue(rule.getSelectors().isEmpty());
        assertTrue(rule.getPropertyValuePairs().isEmpty());
    }
    
    @Test
    public void testRuleFromString() {
        String s = "Selector";
        CssRule rule = new CssRule(s);
        assertEquals(1, rule.getSelectors().size());
        assertEquals(s, rule.getSelectors().get(0));
    }
    
    @Test
    public void testRuleFromList() {
        String s1 = "Selector1";
        String s2 = "Selector2";
        String s3 = "Selector3";
        ArrayList<String> list = new ArrayList<String>();
        list.add(s1);
        list.add(s2);
        list.add(s3);
        CssRule rule = new CssRule(list);
        assertEquals(3, rule.getSelectors().size());
        assertEquals(s2, rule.getSelectors().get(1));
    }
    
    @Test
    public void testRemoveSelector() {
        String s1 = "Selector1";
        String s2 = "Selector2";
        String s3 = "Selector3";
        ArrayList<String> list = new ArrayList<String>();
        list.add(s1);
        list.add(s2);
        list.add(s3);
        CssRule rule = new CssRule(list);
        rule.removeSelector(s2);
        assertEquals(2, rule.getSelectors().size());
        assertFalse(rule.getSelectors().contains(s2));
        assertEquals(s3, rule.getSelectors().get(1));
    }
    
    @Test
    public void testAddSelector() {
        String s1 = "Selector1";
        CssRule rule = new CssRule("Selector");
        rule.addSelector(s1);
        assertEquals(2, rule.getSelectors().size());
        assertTrue(rule.getSelectors().contains(s1));
    }
    
    @Test
    public void testSelectorsAsString() {
        String s1 = "Selector1";
        String s2 = "Selector2";
        String s3 = "Selector3";
        ArrayList<String> list = new ArrayList<String>();
        list.add(s1);
        list.add(s2);
        list.add(s3);
        CssRule rule = new CssRule(list);
        assertEquals(s1 + ", " + s2 + ", " + s3, rule.selectorsAsString());
    }
    
    @Test
    public void testPropertyValue() {
        String property = "Property";
        String value = "Value";
        CssRule rule = new CssRule("Selector");
        
        rule.putPropertyValuePair(property, value);
        assertEquals(1, rule.getPropertyValuePairs().size());
        assertTrue(rule.getPropertyValuePairs().containsKey(property));
        assertEquals(value, rule.getValue(property));
        
        String value2 = "Value 2";
        rule.putPropertyValuePair(property, value2);
        assertEquals(1, rule.getPropertyValuePairs().size());
        assertTrue(rule.getPropertyValuePairs().containsKey(property));
        assertEquals(value2, rule.getValue(property));      
    }
    
    @Test
    public void testPutPropertyValue() {
        String property1 = "Property1";
        String value1 = "Value 1";
        String property2 = "Property2";
        String value2 = "Value 2";
        CssRule rule = new CssRule("Selector");
        
        rule.putPropertyValuePair(property1, value1);
        rule.putPropertyValuePair(property2, value2);
        assertEquals(2, rule.getPropertyValuePairs().size());
        rule.removeProperty(property1);
        assertEquals(1, rule.getPropertyValuePairs().size());
        assertFalse(rule.getPropertyValuePairs().containsKey(property1));
        assertTrue(rule.getPropertyValuePairs().containsKey(property2));
    }
    
    @Rule
    public final ExpectedException exception = ExpectedException.none();
    
    @Test 
    public void testIllegalRemoveSelector(){
        String s = "Selector";
        CssRule rule = new CssRule(s);
        exception.expect(IllegalStateException.class);
        rule.removeSelector(s);
    }
    
    @Test 
    public void testIllegalValue_empty(){
        CssRule rule = new CssRule("Selector");
        exception.expect(IllegalArgumentException.class);
        rule.putPropertyValuePair("something", "");
    }
    
    @Test 
    public void testIllegalProperty_empty(){
        CssRule rule = new CssRule("Selector");
        exception.expect(IllegalArgumentException.class);
        rule.putPropertyValuePair("", "something");
    }
    
    @Test 
    public void testIllegalProperty_space(){
        CssRule rule = new CssRule("Selector");
        exception.expect(IllegalArgumentException.class);
        rule.putPropertyValuePair("Space Space", "something");
    }
    
    @Test 
    public void testIllegalProperty_tab(){
        CssRule rule = new CssRule("Selector");
        exception.expect(IllegalArgumentException.class);
        rule.putPropertyValuePair("Tab\tTab", "something");
    }
    
    @Test 
    public void testIllegalProperty_newline(){
        CssRule rule = new CssRule("Selector");
        exception.expect(IllegalArgumentException.class);
        rule.putPropertyValuePair("Newline\nNewline", "something");
    }
    
    @Test 
    public void testIllegalSelector_empty(){
        exception.expect(IllegalArgumentException.class);
        new CssRule("");
    }
    
    @Test 
    public void testIllegalSelector_space(){
        exception.expect(IllegalArgumentException.class);
        new CssRule("Space Space");
    }
    
    @Test 
    public void testIllegalSelector_tab(){
        exception.expect(IllegalArgumentException.class);
        new CssRule("Tab\tTab");
    }
    
    @Test 
    public void testIllegalSelector_newline(){
        exception.expect(IllegalArgumentException.class);
        new CssRule("Newline\nNewline");
    }
}
