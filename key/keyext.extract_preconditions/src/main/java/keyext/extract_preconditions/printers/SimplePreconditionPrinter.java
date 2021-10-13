package keyext.extract_preconditions.printers;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.LogicPrinter;
import org.key_project.util.collection.ImmutableList;

public class SimplePreconditionPrinter implements PreconditionPrinter {

    private Services termServices;

    public SimplePreconditionPrinter(Services services) {
        this.termServices = services;
    }

    @Override
    public void print(ImmutableList<Term> preconditionList) {
        System.out
            .println(LogicPrinter.quickPrintTerm(
                this.termServices.getTermBuilder().or(preconditionList),
                this.termServices));
    }
}
