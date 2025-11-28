package org.keyproject.key.api.data;

/**
 * TextRange specifies a range of integer numbers e.g. character positions.
 *
 * @param start this range's (included) start position.
 * @param end   this range's (excluded) end position.
 */
public record TextRange(int start, int end) implements KeYDataTransferObject {
}
