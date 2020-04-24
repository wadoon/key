// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.model;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;

/**
 * @author Dominic Steinhoefel
 */
@XmlRootElement
@XmlAccessorType(value = XmlAccessType.FIELD)
public class FunctionDeclaration extends NullarySymbolDeclaration implements FuncOrPredDecl {
    @XmlAttribute
    private String funcName = "";
    @XmlAttribute
    private String resultSortName = "";
    @XmlElement(name = "argSort")
    private List<String> argSorts = new ArrayList<>();

    FunctionDeclaration() {
    }

    public FunctionDeclaration(String funcName, String resultSortName, List<String> argSorts) {
        this.funcName = funcName;
        this.argSorts = argSorts;
        this.resultSortName = resultSortName;
    }

    public FunctionDeclaration(String funcName, String resultSortName) {
        this(funcName, resultSortName, Collections.emptyList());
    }

    @Override
    public boolean isFuncDecl() {
        return true;
    }

    @Override
    public String getName() {
        return getFuncName();
    }

    @Override
    public String toSeqSingleton() {
        assert argSorts.isEmpty() && resultSortName.equals("LocSet");
        return String.format("seqSingleton(value(%s))", funcName);
    }

    public String getResultSortName() {
        return resultSortName;
    }

    public void setResultSortName(String resultSortName) {
        this.resultSortName = resultSortName;
    }

    public String getFuncName() {
        return funcName;
    }

    public void setFuncName(String funcName) {
        this.funcName = funcName;
    }

    public List<String> getArgSorts() {
        return argSorts;
    }

    public void setArgSorts(List<String> argSorts) {
        this.argSorts = argSorts;
    }

    public static Optional<FunctionDeclaration> fromString(final String str)
            throws IllegalArgumentException {
        final Matcher matcher = getMatcherForStr(str);

        if (!matcher.matches()) {
            return Optional.empty();
        }

        return Optional.of(new FunctionDeclaration(matcher.group(2), matcher.group(1),
                matcher.group(3) == null ? Collections.emptyList()
                        : Arrays.asList(matcher.group(3).replaceAll(" ", "").split(","))));
    }

    /**
     * Matches function declarations like "int test(java.lang.String, int)".
     * 
     * @param str The String that should be matched.
     * @return A matcher; if it "matches()", the group 1 contains the sort, group 2
     *         the name, and group 3 is either null or contains a comma-separated
     *         list of argument types.
     */
    protected static Matcher getMatcherForStr(final String str) {
        final Pattern pattern = Pattern.compile(
                "^ *([a-zA-Z0-9_.]+(?: *\\[\\])?) +([a-zA-Z0-9_]+) *(?:\\( *([a-zA-Z0-9_.]+(?: *\\[\\])?(?: *, *[a-zA-Z0-9_.]+(?: *\\[\\])?)* *)\\))? *$");
        final Matcher matcher = pattern.matcher(str);
        return matcher;
    }

    @Override
    public String toString() {
        if (argSorts.isEmpty()) {
            return String.format("%s %s", resultSortName, funcName);
        }

        return String.format("%s %s(%s)", resultSortName, funcName,
                argSorts.stream().collect(Collectors.joining(", ")));
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof FunctionDeclaration && obj != null
                && ((FunctionDeclaration) obj).toString().equals(toString());
    }
}
