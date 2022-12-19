package keyext.extract_preconditions.printers;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.util.Pair;
import keyext.extract_preconditions.projections.visitors.FindVarNamesVisitor;
import keyext.extract_preconditions.projections.visitors.VarNameVisitor;
import org.key_project.util.collection.ImmutableList;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public class JsonPreconditionPrinter implements PreconditionPrinter {

    private Services services;
    private PrintStream output;

    public JsonPreconditionPrinter(Services services, PrintStream output) {
        this.services = services;
        this.output = output;
    }

    private void printTerm(Term curTerm) {
        VarNameIdentificationVisitor v = new VarNameIdentificationVisitor(this.services);
        curTerm.execPostOrder(v);
        HashMap<String, Sort> variables = v.getSortedTerms();
        output.println("\"variables\":{");
        boolean isFirst=true;
        for (String variableName : variables.keySet()) {
            if (!isFirst) {
                output.println(",");
            }
            output.print("\""+variableName+"\": \""+variables.get(variableName).toString()+"\"");
            isFirst=false;
        }
        output.print("},\n\"term\":\"");
        output
            .print(LogicPrinter.quickPrintTerm(
                this.services.getTermBuilder().or(curTerm),
                this.services)
                .replaceAll("\n\\s*","")
                .replaceAll("\\\\","\\\\\\\\"));
        output.println("\"");
    }

    @Override
    public void print(Pair<ImmutableList<Term>, Map<String, ImmutableList<Term>>> preconditions) {
        output.println("{\"error_preconditions\":[");
        boolean isFirst=true;
        for(Term curPrecond : preconditions.first) {
            if (!isFirst) {
                output.println(",");
            }
            output.println("{");
            this.printTerm(curPrecond);
            output.println("}");
            isFirst=false;
        }
        output.println("],\n\"service_preconditions\":[");
        isFirst=true;
        for (String precondName : preconditions.second.keySet()) {
            for (Term curTerm : preconditions.second.get(precondName)) {
                if (!isFirst) {
                    output.println(",");
                }
                output.println("{");
                output.print("\"service\":\"" + precondName + "\",");
                this.printTerm(curTerm);
                output.println("}");
                isFirst=false;
            }
        }
        output.println("]}");
        Term completeTerm = this.services.getTermBuilder().or(preconditions.first);
        for (String precondName : preconditions.second.keySet()) {
            completeTerm = this.services.getTermBuilder().or(
                completeTerm,
                this.services.getTermBuilder().or(preconditions.second.get(precondName)));
        }
    }

    private class VarNameIdentificationVisitor extends VarNameVisitor {

        public HashMap<String, Sort> sortedTerms;

        private Services services;

        public VarNameIdentificationVisitor(Services servicesParam){
            sortedTerms = new HashMap<String, Sort>();
            services = servicesParam;
        }

        public HashMap<String, Sort> getSortedTerms() {
            return sortedTerms;
        }

        @Override
        public void handleVariables(Set<Name> foundVariables, Set<ProgramVariable> variablesFound,
                                    Set<Function> foundFunctions) {
            // Happens implicitly
        }

        @Override
        protected FindVarNamesVisitor getVarNameVisitor(){
            return new FindVarTypesVisitor(this.sortedTerms, this.services);
        }
    }

    private class FindVarTypesVisitor extends FindVarNamesVisitor {

        public HashMap<String, Sort> sortedTerms;

        private Services services;

        public FindVarTypesVisitor(HashMap<String, Sort> sortedTermsParam, Services servicesParam) {
            sortedTerms = sortedTermsParam;
            services=servicesParam;
        }

        @Override
        public void visit(Term visited) {
            if (isBuiltinObjectProperty(visited)) {
                return;
            }
            if (visited.op() instanceof ProgramVariable) {
                ProgramVariable var = (ProgramVariable) visited.op();
                this.sortedTerms.put(getStringIdentifier(visited), visited.sort());
            }
            if (visited.op() instanceof Function) {
                Function fun = (Function) visited.op();
                Name funName = visited.op().name();
                if (isSelectTerm(visited)){
                    this.sortedTerms.put(getStringIdentifier(visited), fun.sort());
                }
            }
        }

        private String getStringIdentifier(Term t) {
            return LogicPrinter.quickPrintTerm(t,this.services).trim();
        }
    }
}
