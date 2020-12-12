package de.uka.ilkd.key.testgen;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.macros.TestGenMacro;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.smt.testgen.BaseTestGenerator;
import de.uka.ilkd.key.smt.testgen.PrintStreamLog;
import de.uka.ilkd.key.smt.testgen.StopRequest;
import de.uka.ilkd.key.smt.testgen.TestGenerationLog;

import java.io.File;
import java.io.PrintStream;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (12/12/20)
 */
public class PreCondApp {
    static final PrintStream err = System.err;
    static final PrintStream out = System.out;

    public static void main(String[] args) throws ProblemLoaderException, InterruptedException {
        String[] arguments = args;
        if (args.length != 0) {
            err.println("Invalid parameter number.");
            //System.exit(1);
            arguments = new String[]{
                    "/home/weigl/Documents/qarch/casestudies/AgeOfMajority/Maturity.java", "run", "get"
            };
        }

        err.format("Load file: %s%n", arguments[0]);
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(new File(args[0]));
        Proof proof = env.getLoadedProof();

        for (int i = 1; i < arguments.length; i++) {
            err.format("Execute command: %s%n", arguments[i]);
            switch (args[i]) {
                case "run":
                    executeMacro(proof, env.getUi());
                    break;
                case "get":
                    get(proof, env.getUi());
                    break;
            }
        }
    }


    private static void get(Proof proof, UserInterfaceControl ui) {
        BaseTestGenerator tg = null;
        try {
            tg = new BaseTestGenerator(ui, proof);
            TestGenerationLog log = new PrintStreamLog(err);
            StopRequest stopRequest = () -> false;
            List<Proof> proofs = tg.createProofsForTesting(true, true);

            for (Proof p : proofs) {
                out.println(p.toString());
            }

        } finally {
            if (tg != null) {
                tg.dispose();
            }
        }
    }

    private static void executeMacro(Proof proof, UserInterfaceControl ui) throws InterruptedException {
        out.format("Applying TestGen Macro (bounded symbolic execution)...");
        TestGenMacro macro = new TestGenMacro();
        macro.applyTo(ui, proof, proof.openEnabledGoals(), null, null);
        out.println("Finished symbolic execution.");
    }
}

