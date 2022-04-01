package de.uka.ilkd.key.core;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.ui.ConsoleUserInterfaceControl;
import de.uka.ilkd.key.ui.Verbosity;
import py4j.GatewayServer;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.stream.Collectors;

public class KeYPythonGateway {
    public String proveProblem(String fileName) {
        try {
            final String file_content = Files.lines(Paths.get(fileName))
                    .collect(Collectors.joining(System.lineSeparator()));

            System.out.println("Proving problem.");
            System.out.println("File: " + fileName);
            System.out.println(file_content);

            final ConsoleUserInterfaceControl ui = new ConsoleUserInterfaceControl(Verbosity.DEBUG, false);
            final SuccessListener successListener = new SuccessListener();
            ui.addProverTaskListener(successListener);
            final File file = new File(fileName);
            ui.loadProblem(file);

            final String result = ui.allProofsSuccessful ? "Success" : successListener.numOpenGoals + " open goals";
            System.out.println("Result: " + result);
            return result;
        } catch (Exception e) {
            final String msg = "Exception (" + e.getClass().getName() + "): " + e.getMessage();
            System.out.println(msg);
            return msg;
        }
    }

    public static void main(String[] args) {
        final KeYPythonGateway gateway = new KeYPythonGateway();
        final GatewayServer server = new GatewayServer(gateway);
        server.start();
        System.out.println("KeY-Python gateway is running...");
    }

    private static class SuccessListener implements ProverTaskListener {
        private int numOpenGoals = -1;

        @Override
        public void taskStarted(TaskStartedInfo info) {
        }

        @Override
        public void taskProgress(int position) {
        }

        @Override
        public void taskFinished(TaskFinishedInfo info) {
            if (info == null) {
                return;
            }

            if (info.getSource() instanceof ProblemLoader &&
                    info.getResult() instanceof RuntimeException) {
                throw (RuntimeException) info.getResult();
            }

            final Proof proof = info.getProof();

            if (proof == null) {
                return;
            }

            final StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
            sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_DEF_OPS);
            numOpenGoals = proof.openGoals().size();
        }
    }
}
