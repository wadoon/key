package edu.key_project.script.ui;

import org.junit.Test;

import static edu.key_project.script.ui.ScriptUtils.*;
import static org.junit.Assert.*;

/**
 * @author Alexander Weigl
 * @version 1 (02.03.19)
 */
public class ScriptUtilsTest {
    @Test
    public void isCommentedTest() {
        assertTrue(isCommented("// test test"));
        assertTrue(isCommented("// test test\n// abc"));
        assertTrue(isCommented("// test test\n// abc\n"));
        assertTrue(isCommented("// test test\n       // abc\n"));

        assertFalse(isCommented("a // test test"));
        assertFalse(isCommented("abc"));
    }

    @Test
    public void removeCommentsTest() {
        assertEquals("abc", removeComments("//abc"));
        assertEquals("abc\nabc", removeComments("//abc\n//abc"));
    }

    @Test
    public void commentTest() {
        assertEquals("// abc\n// abc", comment("abc\nabc"));
    }
}