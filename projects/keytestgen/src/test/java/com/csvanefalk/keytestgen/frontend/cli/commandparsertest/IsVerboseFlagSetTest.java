package com.csvanefalk.keytestgen.frontend.cli.commandparsertest;

import junit.framework.Assert;
import org.junit.Test;

public class IsVerboseFlagSetTest extends CommandParserTest {

    @Test
    public void testVerboseAbout() {

        String[] args = {"-v"};
        processor.parse(args);
        Assert.assertTrue(commandParser.isVerboseFlagSet());
    }

    @Test
    public void testParseVerboseLong() {

        String[] args = {"--verbose"};
        processor.parse(args);
        Assert.assertTrue(commandParser.isVerboseFlagSet());
    }
}
