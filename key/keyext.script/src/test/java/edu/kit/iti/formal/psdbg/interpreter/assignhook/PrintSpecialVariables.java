package edu.kit.iti.formal.psdbg.interpreter.assignhook;

import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import edu.kit.iti.formal.psdbg.interpreter.InterpreterBuilder;
import edu.kit.iti.formal.psdbg.interpreter.KeyInterpreter;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.parser.ast.ProofScript;
import edu.kit.iti.formal.psdbg.parser.ast.Variable;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import edu.kit.iti.formal.psdbg.parser.types.SimpleType;
import org.junit.Test;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import static edu.kit.iti.formal.psdbg.TestHelper.getFile;

/**
 * @author Alexander Weigl
 * @version 1 (20.11.17)
 */
public class PrintSpecialVariables {
    @Test
    public void printSpecialVariables() throws ProblemLoaderException {
        File f = new File(getFile(getClass(), "../contraposition/contraposition.key"));
        InterpreterBuilder ib = new InterpreterBuilder();
        KeyInterpreter inter = ib.proof(KeYApi.loadFromKeyFile(f).getLoadedProof())
                .startState()
                .build();
        inter.interpret(new ProofScript());
        VariableAssignment va = inter.peekState().getSelectedGoalNode().getAssignments();


        for (VariableAssignmentHook<KeyData> hook : inter.getVariableHooks()) {
            System.out.format("### %s%n%n", hook.toString());
            try {
                DefaultAssignmentHook<KeyData> dfhook = (DefaultAssignmentHook<KeyData>) hook;
                List<String> vars = new ArrayList<>(dfhook.getVariables().keySet());
                vars.sort(String::compareTo);

                for (String varname : vars) {
                    DefaultAssignmentHook.Variable v = dfhook.getVariables().get(varname);
                    Variable var = new Variable(v.getName());
                    Value rt = va.getValue(var);

                    System.out.printf("* `%s : %s = %s`%n%n",
                            v.getName(),
                            rt.getType(),
                            (rt.getType() == SimpleType.STRING
                                    ? ('"' + rt.getData().toString() + '"')
                                    : rt.getData())
                    );


                    String doc = "no documentation";
                    if (v.getDocumentation() != null && !v.getDocumentation().isEmpty())
                        doc = v.getDocumentation().replace("\n", "\n  ");
                    System.out.println("  " + doc);
                    System.out.println();
                }
            } catch (ClassCastException e) {

            }
        }
    }

}