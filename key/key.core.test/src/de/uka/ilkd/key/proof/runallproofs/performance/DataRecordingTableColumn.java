package de.uka.ilkd.key.proof.runallproofs.performance;

/**
 * A column from a {@link DataRecordingTable}, consisting of a type for the data
 * stored in the column and the name of the column.
 */
public class DataRecordingTableColumn<T> {
    final String name;

    DataRecordingTableColumn(String name) {
        this.name = name;
    }
}
