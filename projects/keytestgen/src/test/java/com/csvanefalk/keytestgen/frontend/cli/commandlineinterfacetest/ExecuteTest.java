package com.csvanefalk.keytestgen.frontend.cli.commandlineinterfacetest;

import com.csvanefalk.keytestgen.frontend.cli.CommandLineInterface;
import org.junit.Before;
import org.junit.Test;

public class ExecuteTest extends CommandLineInterFaceTest {

    CommandLineInterface cli = null;

    String path = "/Users/christopher/IdeaProjects/keytestgen/src/test/java/com/csvanefalk/keytestgen/targetmodels/own/";

    @Before
    public void setup() {

        cli = new CommandLineInterface();
    }

    //@Test
    public void generateAllIntegerMethodsOneFile() {

        String[] args = {"/home/christopher/git/key/projects/KeYTestGen/test/se/gu/svanefalk/testgeneration/targetmodels/JavaUtilClass.java/"};

        cli.main(args);
    }

    @Test
    public void generateAllUtilMethodsOneFile() {

        String[] args = {path + "IntegerClass.java"};

        cli.main(args);
    }
}
