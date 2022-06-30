package org.key_project.slicing;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.core.Log;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.util.CommandLine;
import de.uka.ilkd.key.util.CommandLineException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.nio.file.Files;

public final class Main {
    private Main() { }

    private static final String HELP = "--help";

    private static final Logger LOGGER = LoggerFactory.getLogger(Main.class);

    public static void main(String[] args) {
        try {
            var cl = createCommandLine();
            cl.parse(args);
            Log.configureLogging(2);
            evaluateOptions(cl);
            var fileArguments = cl.getFileArguments();
            for (var file : fileArguments) {
                try {
                    processFile(file);
                } catch (Exception e) {
                    LOGGER.error("error occurred in slicing", e);
                }
            }
        } catch (ExceptionInInitializerError e) {
            LOGGER.error("D'oh! It seems that KeY was not built properly!", e);
            System.exit(777);
        } catch (CommandLineException e) {
            LOGGER.error("Error in parsing the command: {}", e.getMessage());
        }
    }

    private static void processFile(File proofFile) throws Exception {
        LOGGER.info("Processing proof: {}", proofFile.getName());
        GeneralSettings.noPruningClosed = false;
        DependencyTracker tracker = new DependencyTracker();
        KeYEnvironment<?> environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFile, null, null, null, null, null, proof -> proof.addRuleAppListener(tracker), true);
        try {
            // get loaded proof
            Proof proof = environment.getLoadedProof();
            // analyze proof
            var results = tracker.analyze();
            // slice proof
            var saved = tracker.sliceProof();
            KeYEnvironment<?> environment2 = KeYEnvironment.load(JavaProfile.getDefaultInstance(), saved.toFile(), null, null, null, null, null, proof2 -> proof2.addRuleAppListener(tracker), true);
            // TODO
            Proof slicedProof = environment2.getLoadedProof();

            // reload proof to verify the slicing was correct
            var tempFile = Files.createTempFile("", ".proof");
            slicedProof.saveToFile(tempFile.toFile());
            KeYEnvironment<?> loadedEnvironment = KeYEnvironment.load(JavaProfile.getDefaultInstance(), tempFile.toFile(), null, null, null, null, null, null, true);
            try {
                slicedProof = loadedEnvironment.getLoadedProof();
                LOGGER.info("Original proof: {} steps, {} branch(es)", proof.countNodes() - proof.allGoals().size(), proof.countBranches());
                LOGGER.info("Sliced proof: {} steps, {} branch(es)", slicedProof.countNodes() - slicedProof.allGoals().size(), slicedProof.countBranches());

                Files.delete(tempFile);
            } finally {
                loadedEnvironment.dispose();
            }
        } finally {
            environment.dispose();
        }
    }

    private static CommandLine createCommandLine() {
        var cl = new CommandLine();
        cl.setIndentation(3);
        cl.addSection("Using KeY's proof slicer");
        cl.addText("Usage: ./key [options] [filename]\n\n", false);
        cl.addSection("Options");
        cl.addOption(HELP, null, "display this text");
        //cl.addOption(OUTPUT, "<filename>", "output file (required)");
        return cl;
    }

    private static void evaluateOptions(CommandLine cl) {
        if (cl.getFileArguments().isEmpty()) {
            LOGGER.error("need at least one proof file");
            System.exit(1);
        }
    }
}
