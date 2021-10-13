package keyext.extract_preconditions.printers;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import keyext.extract_preconditions.projections.visitors.FindVarNamesVisitor;
import keyext.extract_preconditions.projections.visitors.VarNameVisitor;
import org.key_project.util.collection.ImmutableList;

import java.util.HashMap;
import java.util.Set;

public class JsonPreconditionPrinter implements PreconditionPrinter {

    private Services termServices;

    public JsonPreconditionPrinter(Services services) {
        this.termServices = services;
    }

    @Override
    public void print(ImmutableList<Term> preconditionList) {
        Term disjunction = this.termServices.getTermBuilder().or(preconditionList);
        VarNameIdentificationVisitor v = new VarNameIdentificationVisitor();
        disjunction.execPostOrder(v);
        HashMap<Term,Sort> variables = v.getSortedTerms();
        System.out.println("{\"variables\":{");
        boolean isFirst=true;
        for (Term variableName : variables.keySet()) {
            if (!isFirst) {
                System.out.println(",");
            }
            System.out.print("\""+LogicPrinter.quickPrintTerm(variableName, this.termServices).trim()+"\": \""+variables.get(variableName).toString()+"\"");
            isFirst=false;
        }
        System.out.print("},\n\"precondition\":\"");
        System.out
            .print(LogicPrinter.quickPrintTerm(
                this.termServices.getTermBuilder().or(preconditionList),
                this.termServices).replaceAll("\n",""));
        System.out.print("\"}");
    }

    private class VarNameIdentificationVisitor extends VarNameVisitor {

        public HashMap<Term, Sort> sortedTerms;

        public VarNameIdentificationVisitor(){
            sortedTerms = new HashMap<>();
        }

        public HashMap<Term, Sort> getSortedTerms() {
            return sortedTerms;
        }

        @Override
        public void handleVariables(Set<Name> foundVariables, Set<ProgramVariable> variablesFound,
                                    Set<Function> foundFunctions) {
            // Happens implicitly
        }

        @Override
        protected FindVarNamesVisitor getVarNameVisitor(){
            return new FindVarTypesVisitor(this.sortedTerms);
        }
    }

    private class FindVarTypesVisitor extends FindVarNamesVisitor {

        public HashMap<Term, Sort> sortedTerms;

        public FindVarTypesVisitor(HashMap<Term, Sort> sortedTermsParam) {
            sortedTerms = sortedTermsParam;
        }

        @Override
        public void visit(Term visited) {
            if (isBuiltinObjectProperty(visited)) {
                return;
            }
            if (visited.op() instanceof ProgramVariable) {
                ProgramVariable var = (ProgramVariable) visited.op();
                this.sortedTerms.put(visited, visited.sort());
            }
            if (visited.op() instanceof Function) {
                Function fun = (Function) visited.op();
                Name funName = visited.op().name();
                if (isSelectTerm(visited)){
                    this.sortedTerms.put(visited, fun.sort());
                }
            }
        }
    }
}
