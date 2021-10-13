package keyext.extract_preconditions.printers;

import de.uka.ilkd.key.logic.Term;
import org.key_project.util.collection.ImmutableList;

public interface PreconditionPrinter {
    void print(ImmutableList<Term> preconditionList);
}
