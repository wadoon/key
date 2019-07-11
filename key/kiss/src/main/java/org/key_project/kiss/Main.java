package org.key_project.kiss;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;

/**
 * Key interactive script shell.
 *
 * @author weigl
 */
public class Main {
    private static final RuntimeException proofClosedException = new RuntimeException();


    public static void main(String[] args) throws ProblemLoaderException, InterruptedException, ScriptException, IOException {
        if (args.length != 1) {
            System.out.println("Usage: ./kiss <file.proof>");
            System.exit(1);
        }

        KeYEnvironment<?> env = KeYEnvironment.load(new File(args[0]));
        Proof proof = env.getLoadedProof();
        try {
            System.out.println(">>> Proof loaded. Waiting for commands");
            runShell(proof);
        } finally {
            env.dispose(); // Ensure always that all instances of KeYEnvironment are disposed
        }
    }

    private static void runShell(Proof proof) throws InterruptedException, ScriptException, IOException {
        ProofScriptEngine pse = new ProofScriptEngine(new InputStreamReader(System.in),
                new Location("<interactive>", -1, -1)) {
            @Override
            protected void afterCommandApplication(ProofScriptCommand<Object> command, Object arg, Node firstNode) {
                if (proof.closed()) {
                    throw proofClosedException;
                }
            }
        };
        try {
            pse.execute(new DefaultUserInterfaceControl(), proof);
        } catch (ScriptException e) {
            if (e.getCause() != proofClosedException) {
                throw e;
            } else {
                System.out.println("Proof is closed");
            }
        }
    }
}


