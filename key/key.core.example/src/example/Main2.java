package example;

import de.uka.ilkd.key.api.*;
import de.uka.ilkd.key.macros.scripts.RuleCommand;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

import java.io.File;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Created by sarah on 5/4/17.
 */
public class Main2 {
    static final File testFile = new File("/home/sarah/Documents/KIT_Mitarbeiter/KeYDevelopment/KeYGitDir/key/key/key.ui/examples/standard_key/prop_log/contraposition.key");
    static  ProofManagementApi api;

        public static void main(String[] args) {
            try {

                api = KeYApi.loadFromKeyFile(testFile);
                ProofApi papi= api.getLoadedProof();
                ScriptApi scrapi = papi.getScriptApi();
                System.out.println(papi.getFirstOpenGoal().getSequent().toString());
                List<ProjectedNode> openGoals = papi.getOpenGoals();
                for (ProjectedNode openGoal : openGoals) {
                    RuleCommand rc = (RuleCommand)
                    KeYApi.getScriptCommandApi().getScriptCommands("rule");
                    Map cArgs = new HashMap<>();
                    VariableAssignments va = new VariableAssignments();
                    cArgs.put("#2", "impRight");
                    cArgs.put("on", openGoal.getSequent());
                    ProofScriptCommandCall impRight = scrapi.instantiateCommand(rc, cArgs);
                    scrapi.executeScriptCommand(impRight, openGoal, va);
                    System.out.println(papi.getFirstOpenGoal().getSequent());
                }

            } catch (ProblemLoaderException e) {
                System.out.println("Could not load file");
            } catch (Exception e) {
                e.printStackTrace();
            }
        }
}
