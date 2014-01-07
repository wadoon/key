package com.csvanefalk.keytestgen.frontend.cli.commandparsertest;

import junit.framework.Assert;
import org.junit.Test;

public class IsHelpFlagSetTest extends CommandParserTest {

    @Test
    public void testParseHelp() {

        String[] args = {"-h"};
        processor.parse(args);
        Assert.assertTrue(commandParser.isHelpFlagSet());
    }

    @Test
    public void testParseHelpLong() {

        String[] args = {"--help"};
        processor.parse(args);
        Assert.assertTrue(commandParser.isHelpFlagSet());
    }
}
