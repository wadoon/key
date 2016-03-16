package de.uka.ilkd.key.nui.test;

import static org.junit.Assert.*;

import java.util.ArrayList;

import org.junit.Test;

import de.uka.ilkd.key.nui.filter.PrintFilter;

public class FilterTest {

    @Test
    public void testPrintFilter_name() {
        PrintFilter filter = new PrintFilter();
        String name = "Name";
        filter.setName(name);
        assertEquals(name, filter.getName());
        
        String name2 = "Name2";
        filter.setName(name2);
        assertEquals(name2, filter.getName());
    }
    
    @Test
    public void testPrintFilter_searchText() {
        PrintFilter filter = new PrintFilter();
        String text = "Text";
        filter.setSearchText(text);
        assertEquals(text, filter.getSearchText());
        
        String text2 = "Text2";
        filter.setSearchText(text2);
        assertEquals(text2, filter.getSearchText());
    }
    
    @Test
    public void testPrintFilter_isUserCriteria() {
        PrintFilter filter = new PrintFilter();
        filter.setIsUserCriteria(false);
        assertFalse(filter.getIsUserCriteria());
        filter.setIsUserCriteria(true);
        assertTrue(filter.getIsUserCriteria());
    }
    
    @Test
    public void testPrintFilter_before() {
        PrintFilter filter = new PrintFilter();
        filter.setBefore(7);
        assertEquals(7, filter.getBefore());
    }
    
    @Test
    public void testPrintFilter_after() {
        PrintFilter filter = new PrintFilter();
        filter.setAfter(7);
        assertEquals(7, filter.getAfter());
    }
    
    @Test
    public void testPrintFilter_invert() {
        PrintFilter filter = new PrintFilter();
        filter.setInvert(false);
        assertFalse(filter.getInvert());
        filter.setInvert(true);
        assertTrue(filter.getInvert());
    }
    
    @Test
    public void testPrintFilter_scope() {
        PrintFilter filter = new PrintFilter();
        filter.setScope(PrintFilter.DisplayScope.AST);
        assertEquals(PrintFilter.DisplayScope.AST, filter.getScope());
        filter.setScope(PrintFilter.DisplayScope.None);
        assertEquals(PrintFilter.DisplayScope.None, filter.getScope());
        filter.setScope(PrintFilter.DisplayScope.Text);
        assertEquals(PrintFilter.DisplayScope.Text, filter.getScope());
    }
    
    @Test
    public void testPrintFilter_filterLayout() {
        PrintFilter filter = new PrintFilter();
        filter.setInvert(false);
        assertFalse(filter.getInvert());
        filter.setInvert(true);
        assertTrue(filter.getInvert());
    }
    
    @Test
    public void testPrintFilter_selections() {
        PrintFilter filter = new PrintFilter();
        String s1 = "Selection1";
        String s2 = "Selection2";
        String s3 = "Selection3";
        ArrayList<String> list = new ArrayList<String>();
        list.add(s1);
        list.add(s2);
        list.add(s3);
        
        filter.setSelections(list);
        assertEquals(list, filter.getSelections());
        //repeat for branch coverage
        filter.setSelections(list);
        assertEquals(list, filter.getSelections());      
    }
    
    @Test
    public void testPrintFilter_clone() {
        PrintFilter filter = new PrintFilter();
        PrintFilter filter2 = filter.cloneFilter();
        assertEquals(filter.getAfter(), filter2.getAfter());
        assertEquals(filter.getBefore(), filter2.getBefore());
        assertEquals(filter.getFilterLayout(), filter2.getFilterLayout());
        assertEquals(filter.getInvert(), filter2.getInvert());
        assertEquals(filter.getIsUserCriteria(), filter2.getIsUserCriteria());
        assertEquals(filter.getName(), filter2.getName());
        assertEquals(filter.getScope(), filter2.getScope());
        assertEquals(filter.getSearchText(), filter2.getSearchText());
        assertEquals(filter.getSelections(), filter2.getSelections());
        assertFalse(filter == filter2);
    }
    
}
