/*
 * KEY
 */

/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.regex.Pattern;

import de.uka.ilkd.key.logic.sort.Sort;

/**
 * This class models s-expressions to be used for the SMT translation.
 * <p>
 * Every s-expression has got a {@link #name} and a (potentially empty) list of
 * {@link #children}.
 * <p>
 * They can be printed out, non-simple names are escaped for SMT.
 *
 * @author Mattias Ulbrich
 */
public class SExpr implements Writable {

    public enum Type {
        INT, BOOL, FLOAT, DOUBLE, UNIVERSE, PATTERN, NONE
    }

    private static final Pattern EXTRACHAR_PATTERN =
        Pattern.compile("[^-A-Za-z0-9+/*=%?!.$_~&^<>@]");

    private final String name;
    private final Type type;

    private List<SExpr> children;

    public SExpr(String name, Type type) {
        this.name = name;
        this.type = type;
        this.children = Collections.emptyList();
    }

    public SExpr(String name) {
        this(name, Type.NONE);
    }

    public SExpr(String name, Type type, List<SExpr> children) {
        this.name = name;
        this.type = type;
        this.children = children;
    }

    public SExpr(String name, List<SExpr> children) {
        this(name, Type.NONE, children);
    }

    public SExpr(String name, Type type, String... children) {
        this.name = name;
        this.type = type;
        this.children = new ArrayList<>();
        for (String string : children) {
            this.children.add(new SExpr(string));
        }
    }

    public SExpr(String name, String... children) {
        this(name, Type.NONE, children);
    }

    public SExpr(String name, Type type, SExpr... children) {
        this(name, type, Arrays.asList(children));
    }

    public SExpr(String name, SExpr... children) {
        this(name, Type.NONE, children);
    }

    public SExpr(SExpr... children) {
        this("", Type.NONE, children);
    }

    public SExpr(List<SExpr> children) {
        this("", Type.NONE, children);
    }

    static SExpr patternSExpr(SExpr e, SExpr... patterns) {
        return new SExpr("! " + e.toString() + " :pattern ", Type.PATTERN, new SExpr(patterns));
    }

    static SExpr sortExpr(Sort sort) {
        return new SExpr(ModularSMTLib2Translator.SORT_PREFIX + sort.toString());
    }

    static SExpr castExpr(SExpr sortExp, SExpr exp) {
        // REVIEW MU: Should there perhaps be a coercion to Universe before the call?
        // What if a "Int" is given. That would fail.
        return new SExpr("cast", Type.UNIVERSE, exp, sortExp);
    }

    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();
        appendTo(sb);
        return sb.toString();
    }

    private String getEscapedName() {
        if (name.length() > 0 && name.charAt(0) == '|' && name.charAt(name.length() - 1) == '|') {
            return name; //already escaped
        }

        if (EXTRACHAR_PATTERN.matcher(name).find() && type != Type.PATTERN && type != Type.DOUBLE && type != Type.FLOAT) {
            return "|" + name + "|";
        } else {
            return name;
        }
    }

    @Override
    public void appendTo(StringBuffer sb) {
        boolean noSpace = name.isEmpty();
        if (children.size() > 0 || noSpace) {
            sb.append("(").append(getEscapedName());
            for (SExpr child : children) {
                if (!noSpace) {
                    sb.append(" ");
                } else {
                    noSpace = false;
                }
                child.appendTo(sb);
            }
            sb.append(")");
        } else {
            sb.append(getEscapedName());
        }
    }

    public Type getType() {
        return type;
    }
}
