package se.gu.svanefalk.testgeneration.frontend.cli.commandparsertest;

import org.junit.Before;

import se.gu.svanefalk.testgeneration.frontend.cli.CLITest;
import se.gu.svanefalk.testgeneration.frontend.cli.CommandParser;

import com.beust.jcommander.JCommander;

public class CommandParserTest extends CLITest {

    protected CommandParser commandParser = null;
    protected JCommander processor = null;

    @Before
    public void setup() {
        commandParser = new CommandParser();
        processor = new JCommander(commandParser);
    }

}
