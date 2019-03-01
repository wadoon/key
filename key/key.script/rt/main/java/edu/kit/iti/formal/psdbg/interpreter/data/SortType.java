package edu.kit.iti.formal.psdbg.interpreter.data;

import de.uka.ilkd.key.logic.sort.Sort;
import edu.kit.iti.formal.psdbg.parser.types.Type;
import lombok.Getter;
import lombok.RequiredArgsConstructor;

@RequiredArgsConstructor
public class SortType implements Type {
    @Getter
    private final Sort sort;

    @Override
    public String symbol() {
        return sort.toString();
    }

    @Override
    public String interpreterSort() {
        return symbol();
    }
}
