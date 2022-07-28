package org.key_project.slicing.util;

import java.util.Objects;

public final class NoHashCode<T> {
    private final T inner;

    public NoHashCode(T obj) {
        this.inner = obj;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        var that = (NoHashCode<?>) o;
        return Objects.equals(inner, that.inner);
    }

    @Override
    public int hashCode() {
        return 0; // this is the entire purpose of the class
    }
}
