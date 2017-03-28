package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Proof;

/**
 *
 */
public class SchemaVarCommand
        extends AbstractCommand<SchemaVarCommand.Parameters> {

    public static class Parameters {
        @ValueInjector.Option("#2") String type;
        @ValueInjector.Option("#3") String var;
    }

    @Override public Parameters evaluateArguments(EngineState state,
            Map<String, String> arguments) throws ScriptException {
        return state.getValueInjector().inject(new Parameters(), arguments);
    }

    @Override public void execute(Parameters args)
            throws ScriptException, InterruptedException {

        if (args.type == null || args.var == null) {
            throw new ScriptException("Missing argument: type var");
        }

        AbbrevMap abbrMap = state.getAbbreviations();

        if (!args.var.matches("@[a-zA-Z0-9_]")) {
            throw new ScriptException("Illegal variable name: " + args.var);
        }

        Name schemaVar = new Name("_SCHEMA_" + args.var.substring(1));

        try {
            SchemaVariable sv;
            if ("Formula".equals(args.type)) {
                sv = SchemaVariableFactory.createFormulaSV(schemaVar);
            }
            else {
                Sort sort = state.toSort(args.type);
                sv = SchemaVariableFactory.createTermSV(schemaVar, sort);
            }

            Term term = state.getProof().getServices().getTermFactory()
                    .createTerm(sv);

            abbrMap.put(term, args.var, true);
        }
        catch (Exception e) {
            throw new ScriptException(e);
        }

    }

    @Override public String getName() {
        return "schemaVar";
    }

}
