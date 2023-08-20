/*
 * KEY
 */

/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package de.uka.ilkd.key.smt.newsmt2;

/**
 * Objects of this class are writable (like {@link SExpr}s), but are not really structured as such.
 * They are just arbitrary strings.
 * <p>
 * Writing them is obvious.
 */
record VerbatimSMT(String string) implements Writable {

    @Override
    public void appendTo(StringBuilder sb) {
        sb.append(string);
    }
}
