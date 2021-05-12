package keyext.extract_preconditions;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.macros.FullAutoPilotProofMacro;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import java.io.File;

public class ExtractorTest {
    public static void main(String[] args) {
        if (args.length <= 0) {
            System.out.println("No file provided");
            return;
        }
        String javaFileName = args[0];
        File javaFile = new File(javaFileName);
        if (!javaFile.exists()) {
            System.out.println("Unable to find file "+javaFileName);
            return;
        }
        ProofMacro autoPilot = new FullAutoPilotProofMacro();
        DefaultUserInterfaceControl uiControl = new DefaultUserInterfaceControl();
        System.out.println("Loading file "+javaFileName+"...");
        AbstractProblemLoader loaderResult;
        try {
            loaderResult =
                uiControl.load(null, javaFile, null, null, null, null, false);
        } catch (ProblemLoaderException e) {
            System.out.println("Failed to load file:");
            e.printStackTrace();
        }
        System.out.println("Loaded file.");
        return;
    }
}
