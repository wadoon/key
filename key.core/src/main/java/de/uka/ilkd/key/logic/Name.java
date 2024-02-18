/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import org.jspecify.annotations.NullMarked;

import java.util.Objects;

/**
 * A Name object is created to represent the name of an object which usually implements the
 * interface {@link Named}.
 *
 * <p>
 * It wraps a string object. To save memory and to speed up equality checks, the wrapped strings are
 * stored in their {@linkplain String#intern() interned} representation.
 */
@NullMarked
public class Name implements Comparable<Name> {
    private static final String NONAME = "_noname_";
    public static final String SCOPE_DELIM = "#";

    private final String identifier;
    private final String scope;

    public Name(String identifier, String scope) {
        this.identifier = identifier.intern();
        this.scope = scope.intern();
    }

    /**
     * creates a name object
     */
    public Name(String name) {
        var parts = name.split(SCOPE_DELIM);
        this.identifier = parts[1].intern();
        this.scope = parts[0].intern();
    }

    @Override
    public String toString() {
        return scope + SCOPE_DELIM + identifier;
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof Name)) {
            return false;
        }
        // since ALL nameStrings are interned, equality can be safely reduced to
        // identity in THIS case:
        return Objects.equals(identifier, ((Name) o).identifier);
    }

    @Override
    public int compareTo(Name o) {
        return identifier.compareTo(o.identifier);
    }

    @Override
    public int hashCode() {
        return identifier.hashCode();
    }

    public boolean isGlobal() {
        return getScope().isBlank();
    }

    public String getScope() {
        return scope;
    }

    public String getIdentifier() {
        return identifier;
    }

    public Name withScope(String newScope) {
        return new Name(identifier, newScope);
    }
}
