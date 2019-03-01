package edu.kit.iti.formal.psdbg.interpreter;

import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.api.ProjectedNode;
import de.uka.ilkd.key.api.ProofApi;
import de.uka.ilkd.key.api.ProofManagementApi;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.parser.Facade;
import edu.kit.iti.formal.psdbg.parser.ast.ProofScript;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import java.io.File;
import java.io.IOException;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (28.05.17)
 */
public class Execute {
    private InterpreterBuilder interpreterBuilder = new InterpreterBuilder();
    private List<String> keyFiles;
    private File scriptFile;

    public static void main(String[] args) throws IOException, ParseException {
        Execute execute = new Execute();
        execute.init(args);
        execute.run();
    }

    public static Options argparse() {
        Options options = new Options();
        options.addOption("h", "--help", false, "print help text");
        options.addOption("p", "--script-path", true, "include folder for scripts");
        options.addOption("l", "--linter", false, "run linter before execute");
        options.addOption("s", "--script", true, "script sourceName");
        return options;
    }

    public Interpreter<KeyData> run() {
        try {
            ProofManagementApi pma = KeYApi.loadFromKeyFile(new File(keyFiles.get(0)));
            ProofApi pa = pma.getLoadedProof();
            ProjectedNode root = pa.getFirstOpenGoal();

            List<ProofScript> ast = Facade.getAST(scriptFile);
            interpreterBuilder.proof(pa).macros()
                    .scriptCommands()
                    .addProofScripts(ast)
                    .scriptSearchPath(new File("."));

            //pa.getProof().getProofIndependentSettings().getGeneralSettings().setOneStepSimplification(false);

            Interpreter<KeyData> inter = interpreterBuilder.startState().build();
            inter.interpret(ast.get(0));
            return inter;
        } catch (ProblemLoaderException | IOException e) {
            e.printStackTrace();
        }
        return null;
    }

    public void init(String[] args) throws ParseException, IOException {
        Options o = argparse();
        DefaultParser parser = new DefaultParser();
        CommandLine cli = parser.parse(o, args);
        keyFiles = cli.getArgList();
        scriptFile = new File(cli.getOptionValue("s"));
        if (cli.getOptionValue('p') != null)
            interpreterBuilder.scriptSearchPath(new File(cli.getOptionValue('p')));
    }
}
