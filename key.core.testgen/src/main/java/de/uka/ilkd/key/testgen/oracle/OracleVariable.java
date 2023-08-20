package de.uka.ilkd.key.testgen.oracle;

import de.uka.ilkd.key.logic.sort.Sort;

public record OracleVariable(String name, Sort sort) implements OracleTerm {

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        OracleVariable other = (OracleVariable) obj;
        if (name == null) {
            if (other.name != null) {
                return false;
            }
        } else if (!name.equals(other.name)) {
            return false;
        }
        if (sort == null) {
            return other.sort == null;
        } else {
            return sort.equals(other.sort);
        }
    }

    public String toString() {
        return name;
    }


}
