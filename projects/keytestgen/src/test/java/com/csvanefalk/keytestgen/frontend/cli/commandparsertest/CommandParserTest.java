package com.csvanefalk.keytestgen.frontend.cli.commandparsertest;

import com.beust.jcommander.JCommander;
import com.csvanefalk.keytestgen.frontend.cli.CLITest;
import com.csvanefalk.keytestgen.frontend.cli.CommandParser;
import org.junit.Before;

public class CommandParserTest extends CLITest {

    protected CommandParser commandParser = null;
    protected JCommander processor = null;

    @Before
    public void setup() {
        commandParser = new CommandParser();
        processor = new JCommander(commandParser);
    }

}
