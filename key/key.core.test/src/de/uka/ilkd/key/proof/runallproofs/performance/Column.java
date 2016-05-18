package de.uka.ilkd.key.proof.runallproofs.performance;

import java.sql.PreparedStatement;
import java.sql.SQLException;

public abstract class Column<T> {
    final String label;
    final String type;
    protected final int index;

    Column(String label, String type, int index) {
        this.label = label;
        this.type = type;
        this.index = index;
    }

    void set(Row row, PreparedStatement stmt) throws SQLException {
        @SuppressWarnings("unchecked")
        T t = (T) row.columnValues.get(label);
        if (t == null) {
            throw new NullPointerException("Column value not declared: " + label);
        }
        setValue(t, stmt);
    }

    abstract void setValue(T t, PreparedStatement stmt) throws SQLException;
}