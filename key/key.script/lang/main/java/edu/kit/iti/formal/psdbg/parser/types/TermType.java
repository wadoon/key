package edu.kit.iti.formal.psdbg.parser.types;

import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (15.08.17)
 */
@AllArgsConstructor
@NoArgsConstructor
@Data
public class TermType implements Type {
    private List<Type> argTypes = new ArrayList<>();

    public TermType(Type... sortType) {
        this(Arrays.asList(sortType));
    }

    @Override
    public String symbol() {
        return "Term<" +
                argTypes.stream().map(Type::symbol).reduce((a, b) -> (a + "," + b)).orElse("")
                + ">";
    }

    @Override
    public String interpreterSort() {
        return argTypes.get(0).interpreterSort();
    }
}
