package keyext.extract_preconditions.printers;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableList;

import java.util.Map;

public class SimplePreconditionPrinter implements PreconditionPrinter {

    private Services termServices;

    public SimplePreconditionPrinter(Services services) {
        this.termServices = services;
    }

    @Override
    public void print(Pair<ImmutableList<Term>, Map<String, ImmutableList<Term>>> preconditions) {
        System.out.println("Failure:");
        System.out
            .println(LogicPrinter.quickPrintTerm(
                this.termServices.getTermBuilder().or(preconditions.first), this.termServices));
        for (String precondName : preconditions.second.keySet()) {
            System.out.println(precondName+":");
            System.out
                .println(LogicPrinter.quickPrintTerm(
                    this.termServices.getTermBuilder().or(preconditions.second.get(precondName)), this.termServices));
        }
    }
}
