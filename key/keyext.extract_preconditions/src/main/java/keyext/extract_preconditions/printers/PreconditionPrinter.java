package keyext.extract_preconditions.printers;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableList;

import java.util.Map;

public interface PreconditionPrinter {
    void print(Pair<ImmutableList<Term>, Map<String, ImmutableList<Term>>> preconditionList);
}
