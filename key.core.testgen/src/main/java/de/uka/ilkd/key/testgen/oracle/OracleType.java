package de.uka.ilkd.key.testgen.oracle;

import de.uka.ilkd.key.logic.sort.Sort;

public record OracleType(Sort s) implements OracleTerm {

    public String toString() {

        return s.name().toString();

    }

}
