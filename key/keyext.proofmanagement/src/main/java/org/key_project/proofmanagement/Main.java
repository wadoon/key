package org.key_project.proofmanagement;
    // TODO: the checkstyle regex for package name does neither allow proof_management nor proofManagement
    // Is this intended?

import java.io.IOException;
import java.net.URISyntaxException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.ResourceBundle;

import de.uka.ilkd.key.util.CommandLine;
import de.uka.ilkd.key.util.CommandLineException;
import org.key_project.proofmanagement.check.*;
import org.key_project.proofmanagement.io.ProofBundleHandler;
import org.key_project.proofmanagement.io.LogLevel;
import org.key_project.proofmanagement.io.HTMLReport;
import org.key_project.proofmanagement.merge.ProofBundleMerger;

/**
 * This is the starting class for ProofManagement.
 * <br>
 * CLI commands:
 *  check [--settings] [--dependency] [--report <out_path>] <bundle_path>
 *    options:
 *        --settings settings check
 *        --dependency dependency check
 *        --auto try to use automode to close open proofs
 *        --explicit (implies a) stores automatically found proofs explicitly as files
 *        --report generate html report + API
 *        --missing check for contracts that have no proof
 *    checks that are always enabled:
 *        - check for duplicate proofs of the same contracts
 *    individually and independently trigger different checks
 *  merge [--force] [--no-check] <bundle1> <bundle2> ... <output>
 *    options:
 *        --force merge the bundles even when the consistency check failed
 *        --check "<check_options>" passes the given options to the check command and
 *                  executes it
 *  bundle [--check]
 *    options:
 *        --check "<check_options>" passes the given options to the check command and
 *                  executes it
 *
 * @author Wolfram Pfeifer
 */
public final class Main {
    /** resource bundle where the description strings for the CLI are stored */
    private static final ResourceBundle STRINGS = ResourceBundle.getBundle("strings");

    /** usage string for general pm command */
    private static final String USAGE = STRINGS.getString("usage");

    /** usage string for check subcommand */
    private static final String USAGE_CHECK = STRINGS.getString("usage_check");

    /** usage string for merge subcommand */
    private static final String USAGE_MERGE = STRINGS.getString("usage_merge");

    /** command line of proof management */
    private static final CommandLine CL;

    static {
        // TODO: check todos in CommandLine class
        CL = new CommandLine();
        CL.addSubCommand("check");
        CommandLine check = CL.getSubCommandLine("check");
        check.addOption("--settings", null, STRINGS.getString("check_settings_desc"));
        check.addOption("--dependency", null, STRINGS.getString("check_dependency_desc"));
        check.addOption("--missing", null, STRINGS.getString("check_missing_desc"));
        check.addOption("--replay", null, STRINGS.getString("check_replay_desc"));
        //check.addOption("--auto", null, STRINGS.getString("check_auto_desc"));
        //check.addOption("--explicit", null, STRINGS.getString("check_explicit_desc"));
        check.addOption("--report", "out_path", STRINGS.getString("check_report_desc"));

        CL.addSubCommand("merge");
        CommandLine merge = CL.getSubCommandLine("merge");
        merge.addOption("--force", null, STRINGS.getString("merge_force_desc"));
        merge.addOption("--check", "check_arguments", STRINGS.getString("merge_check_desc"));

        // enable check option forwarding for merge command
        merge.addSubCommand("check");
        CommandLine mergeCheck = merge.getSubCommandLine("check");
        mergeCheck.addOption("--settings", null, STRINGS.getString("check_settings_desc"));
        mergeCheck.addOption("--dependency", null, STRINGS.getString("check_dependency_desc"));
        mergeCheck.addOption("--missing", null, STRINGS.getString("check_missing_desc"));
        mergeCheck.addOption("--replay", null, STRINGS.getString("check_replay_desc"));
        //mergeCheck.addOption("--auto", null, STRINGS.getString("check_auto_desc"));
        //mergeCheck.addOption("--explicit", null, STRINGS.getString("check_explicit_desc"));
        mergeCheck.addOption("--report", "out_path", STRINGS.getString("check_report_desc"));

        // TODO: bundle subcommand
        CL.addSubCommand("bundle");
    }

    private Main() {
    }

    /**
     * Main entry point for ProofManagement.
     * @param args the commandline arguments. See class JavaDoc for a detailed description.
     */
    public static void main(String[] args) {
        try {
            CL.parse(args);
            if (CL.subCommandUsed("check")) {
                check(CL.getSubCommandLine("check"));
            } else if (CL.subCommandUsed("merge")) {
                merge(CL.getSubCommandLine("merge"));
            } else if (CL.subCommandUsed("bundle")) {
                bundle(CL.getSubCommandLine("bundle"));
            } else {
                CL.printUsage(System.out);
            }
        } catch (CommandLineException e) {
            e.printStackTrace();
        }
    }

    // bundle [-c|--check "check_options"] <root_dir> <bundle_path>
    private static void bundle(CommandLine commandLine) {
        // TODO: bundle subcommand

        List<String> arguments = commandLine.getArguments();
        if (arguments.size() != 2) {
            commandLine.printUsage(System.out);
        }
    }

    // check [--settings] [--dependency] [--missing] [--replay] [--report <out_path>] <bundle_path>
    private static void check(CommandLine commandLine) {

        List<String> arguments = commandLine.getArguments();
        if (arguments.size() != 1) {
            commandLine.printUsage(System.out);
        }

        String pathStr = arguments.get(0);

        // we accumulate results in this variable
        CheckerData globalResult = new CheckerData(LogLevel.DEBUG);
        Path bundlePath = Paths.get(pathStr);
        try (ProofBundleHandler pbh = ProofBundleHandler.createBundleHandler(bundlePath)) {

            globalResult.setPbh(pbh);

            // add file tree to result
            globalResult.setFileTree(pbh.getFileTree());

            if (commandLine.isSet("--missing")) {
                new MissingProofsChecker().check(pbh, globalResult);
            }
            if (commandLine.isSet("--settings")) {
                new SettingsChecker().check(pbh, globalResult);
            }
            if (commandLine.isSet("--replay")) {
                new ReplayChecker().check(pbh, globalResult);
            }
            if (commandLine.isSet("--dependency")) {
                new DependencyChecker().check(pbh, globalResult);
            }
            globalResult.print("All checks done!");
            globalResult.print("Global result: " + globalResult.getGlobalState());

            // generate report
            if (commandLine.isSet("--report")) {
                String outFileName = commandLine.getString("--report", "");
                Path output = Paths.get(outFileName).toAbsolutePath();
                try {
                    HTMLReport.print(globalResult, output);
                } catch (IOException | URISyntaxException e) {
                    System.err.println("Error creating the report: ");
                    e.printStackTrace();
                }
            }
        } catch (IOException e) {
            globalResult.print(LogLevel.ERROR, e.getMessage());
            globalResult.print("Error while accessing the proof bundle!");
            globalResult.print("ProofManagement interrupted due to critical error.");
        } catch (ProofManagementException e) {
            globalResult.print(LogLevel.ERROR, e.getMessage());
            globalResult.print("ProofManagement interrupted due to critical error.");
        }
    }

    // merge [-f|--force] [-n|--no-check] [--check "<check_args>"] <bundle1> <bundle2> ... <output>
    private static void merge(CommandLine commandLine) {
        // TODO: merge subcommand
        List<String> arguments = commandLine.getArguments();

        // at least three files!
        if (arguments.size() < 3) {
            commandLine.printUsage(System.out);
        }

        // convert Strings to Paths (for input and output)
        List<Path> inputs = new ArrayList<>();
        for (int i = 0; i < arguments.size() - 1; i++) {
            inputs.add(Paths.get(arguments.get(i)));
        }
        Path output = Paths.get(arguments.get(arguments.size() - 1));

        if (commandLine.isSet("--force")) {
            // TODO:
        }

        // TODO: use result, print message, clean up particularly created zips
        ProofBundleMerger.merge(inputs, output);

        // perform a check with given commands
        if (commandLine.isSet("--check")) {
            String[] temp = commandLine.getString("--check", "").trim().split(" ");
            String[] newArgs = Arrays.copyOfRange(temp, 0,temp.length + 1);
            newArgs[newArgs.length - 1] = output.toString();
            try {
                CommandLine checkCommandLine = commandLine.getSubCommandLine("check");
                checkCommandLine.parse(newArgs);
                check(checkCommandLine);
            } catch (CommandLineException e) {
                e.printStackTrace();
            }
        }

    }
}