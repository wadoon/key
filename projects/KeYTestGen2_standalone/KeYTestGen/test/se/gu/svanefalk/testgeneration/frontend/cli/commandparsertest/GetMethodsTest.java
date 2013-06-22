package se.gu.svanefalk.testgeneration.frontend.cli.commandparsertest;

import java.util.List;

import junit.framework.Assert;

import org.junit.Test;

public class GetMethodsTest extends CommandParserTest {

    @Test
    public void testGetMethodsAll() {

        String[] args = { "-m", "all" };
        processor.parse(args);

        List<String> expectedMethods = getList("all");
        List<String> actualMethods = commandParser.getMethods();

        Assert.assertTrue(assertListEquality(expectedMethods, actualMethods));
    }

    @Test
    public void testGetMethodsAllLong() {

        String[] args = { "--methods", "all" };
        processor.parse(args);

        List<String> expectedMethods = getList("all");
        List<String> actualMethods = commandParser.getMethods();

        Assert.assertTrue(assertListEquality(expectedMethods, actualMethods));
    }

    // @Test
    public void testGetMethodsSpecific() {

        String[] args = { "--methods", "publicMethod", "publicMethod2",
                "protectedMethod", "protectedMethod2", "privateMethod",
                "privateMethod2", "-c", "stat", "hey.java" };
        processor.parse(args);

        List<String> expectedMethods = getList("publicMethod", "publicMethod",
                "protectedMethod", "protectedMethod2", "privateMethod",
                "privateMethod2");
        List<String> actualMethods = commandParser.getMethods();

        Assert.assertTrue(assertListEquality(expectedMethods, actualMethods));
    }

    // @Test
    public void testGetMethodsSpecificLong() {

        String[] args = { "--methods", "all" };
        processor.parse(args);
        Assert.assertTrue(commandParser.isAboutFlagSet());
    }
}
