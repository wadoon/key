package org.key_project.slicing;

import de.uka.ilkd.key.core.Log;
import de.uka.ilkd.key.gui.lemmatagenerator.LemmataAutoModeOptions;
import de.uka.ilkd.key.ui.AbstractMediatorUserInterfaceControl;
import de.uka.ilkd.key.ui.Verbosity;
import de.uka.ilkd.key.util.CommandLine;
import de.uka.ilkd.key.util.CommandLineException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class Main {
    private static final Logger LOGGER = LoggerFactory.getLogger(Main.class);

    private final static String HELP = "--help";
    private final static String OUTPUT = "--output";

    public static void main(String[] args) {
        try {
            var cl = createCommandLine();
            cl.parse(args);
            Log.configureLogging(2);
            System.out.println("hmm");
            LOGGER.info("uh huh");
            /*
            evaluateOptions(cl);
            fileArguments = cl.getFileArguments();
            fileArguments = preProcessInput(fileArguments);
            AbstractMediatorUserInterfaceControl userInterface = createUserInterface(fileArguments);
            loadCommandLineFiles(userInterface, fileArguments);
             */
        } catch (ExceptionInInitializerError e) {
            LOGGER.error("D'oh! It seems that KeY was not built properly!", e);
            System.exit(777);
        } catch (CommandLineException e) {
            LOGGER.error("Error in parsing the command: {}", e.getMessage());
        }
    }

    private static CommandLine createCommandLine() {
        var cl = new CommandLine();
        cl.setIndentation(3);
        cl.addSection("Using KeY's proof slicer");
        cl.addText("Usage: ./key [options] [filename]\n\n", false);
        cl.addSection("Options");
        cl.addOption(HELP, null, "display this text");
        cl.addOption(OUTPUT, "<filename>", "output file (required)");
        return cl;
    }
}
