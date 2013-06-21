package se.gu.svanefalk.testgeneration.frontend.cli.commandparsertest;

import junit.framework.Assert;

import org.junit.Test;

import se.gu.svanefalk.testgeneration.frontend.cli.CommandParser;

import com.beust.jcommander.JCommander;

public class IsAboutFlagSetTest extends CommandParserTest{
    
    @Test
    public void testParseAbout() {

        String[] args = { "-a" };
        processor.parse(args);
        Assert.assertTrue(commandParser.isAboutFlagSet());
    }

    @Test
    public void testParseAboutLong() {

        String[] args = { "--about" };
        processor.parse(args);
        Assert.assertTrue(commandParser.isAboutFlagSet());
    }
}
