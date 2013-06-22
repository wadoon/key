package se.gu.svanefalk.testgeneration.frontend.cli.commandlineinterfacetest;

import org.junit.Before;
import org.junit.Test;

import se.gu.svanefalk.testgeneration.frontend.cli.CommandLineInterface;

public class ExecuteTest extends CommandLineInterFaceTest {

    CommandLineInterface cli = null;

    @Before
    public void setup() {

        cli = new CommandLineInterface();
    }

    @Test
    public void generateAllMethodsOneFile() {

        String[] args = { "/home/christopher/git/key/projects/KeYTestGen/test/se/gu/svanefalk/testgeneration/targetmodels/IntegerClass.java" };

        cli.execute(args);
    }
}
