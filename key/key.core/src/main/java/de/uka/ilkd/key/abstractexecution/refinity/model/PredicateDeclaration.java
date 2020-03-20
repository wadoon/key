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
@XmlAccessorType(XmlAccessType.FIELD)
public class PredicateDeclaration implements FuncOrPredDecl {
    public static final PredicateDeclaration EMPTY_DECL = //
            new PredicateDeclaration("", Collections.emptyList());

    @XmlAttribute
    private String predName = "";
    @XmlElement(name = "argSort")
    private List<String> argSorts = new ArrayList<>();

    PredicateDeclaration() {
    }

    public PredicateDeclaration(String predName, List<String> argSorts) {
        this.predName = predName;
        this.argSorts = argSorts;
    }

    @Override
    public boolean isFuncDecl() {
        return false;
    }

    @Override
    public String getName() {
        return getPredName();
    }

    public String getPredName() {
        return predName;
    }

    public void setPredName(String predName) {
        this.predName = predName;
    }

    public List<String> getArgSorts() {
        return argSorts;
    }

    public void setArgSorts(List<String> argSorts) {
        this.argSorts = argSorts;
    }

    public static Optional<FuncOrPredDecl> fromString(final String str)
            throws IllegalArgumentException {
        final Pattern pattern = Pattern
                .compile("^([a-zA-Z0-9_]+)(?:\\(([a-zA-Z0-9_.]+(?:,[a-zA-Z0-9_.]+)*)\\))?$");
        final Matcher matcher = pattern.matcher(str.replaceAll(" ", ""));

        if (!matcher.matches()) {
            return Optional.empty();
        }

        return Optional.of(new PredicateDeclaration(matcher.group(1),
                matcher.group(2) == null ? Collections.emptyList()
                        : Arrays.asList(matcher.group(2).split(","))));
    }

    @Override
    public String toString() {
        if (argSorts.isEmpty()) {
            return predName;
        }

        return String.format("%s(%s)", predName,
                argSorts.stream().collect(Collectors.joining(", ")));
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof PredicateDeclaration && obj != null
                && ((PredicateDeclaration) obj).toString().equals(toString());
    }
}