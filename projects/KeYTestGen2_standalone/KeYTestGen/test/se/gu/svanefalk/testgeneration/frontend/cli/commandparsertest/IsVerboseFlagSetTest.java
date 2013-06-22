package se.gu.svanefalk.testgeneration.frontend.cli.commandparsertest;

import junit.framework.Assert;

import org.junit.Test;

import se.gu.svanefalk.testgeneration.frontend.cli.CommandParser;

import com.beust.jcommander.JCommander;

public class IsVerboseFlagSetTest extends CommandParserTest {

    @Test
    public void testVerboseAbout() {

        String[] args = { "-v" };
        processor.parse(args);
        Assert.assertTrue(commandParser.isVerboseFlagSet());
    }

    @Test
    public void testParseVerboseLong() {

        String[] args = { "--verbose" };
        processor.parse(args);
        Assert.assertTrue(commandParser.isVerboseFlagSet());
    }
}
