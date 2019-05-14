package org.key_project.script.ui;

import org.junit.Assert;
import org.junit.Test;

import static org.junit.Assert.*;

/**
 * @author Alexander Weigl
 * @version 1 (02.03.19)
 */
public class ScriptUtilsTest {
    @Test
    public void isCommentedTest() {
        assertTrue(ScriptUtils.isCommented("// test test"));
        assertTrue(ScriptUtils.isCommented("// test test\n// abc"));
        assertTrue(ScriptUtils.isCommented("// test test\n// abc\n"));
        assertTrue(ScriptUtils.isCommented("// test test\n       // abc\n"));

        assertFalse(ScriptUtils.isCommented("a // test test"));
        assertFalse(ScriptUtils.isCommented("abc"));
    }

    @Test
    public void removeCommentsTest() {
        Assert.assertEquals("abc", ScriptUtils.removeComments("//abc"));
        Assert.assertEquals("abc\nabc", ScriptUtils.removeComments("//abc\n//abc"));
    }

    @Test
    public void commentTest() {
        Assert.assertEquals("// abc\n// abc", ScriptUtils.comment("abc\nabc"));
    }
}