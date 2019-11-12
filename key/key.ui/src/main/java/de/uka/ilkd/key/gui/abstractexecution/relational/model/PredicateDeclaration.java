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
package de.uka.ilkd.key.gui.abstractexecution.relational.model;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;

/**
 * @author Dominic Steinhoefel
 */
@XmlRootElement
public class PredicateDeclaration {
    public static final PredicateDeclaration EMPTY_DECL = //
            new PredicateDeclaration("", Collections.emptyList());

    private String predName = "";
    private List<String> argSorts = new ArrayList<>();

    PredicateDeclaration() {
    }

    public PredicateDeclaration(String predName, List<String> argSorts) {
        this.predName = predName;
        this.argSorts = argSorts;
    }

    @XmlAttribute
    public String getPredName() {
        return predName;
    }

    public void setPredName(String predName) {
        this.predName = predName;
    }

    @XmlElement(name = "argSort")
    public List<String> getArgSorts() {
        return argSorts;
    }

    public void setArgSorts(List<String> argSorts) {
        this.argSorts = argSorts;
    }

    public static PredicateDeclaration fromString(final String str)
            throws IllegalArgumentException {
        final Pattern pattern = Pattern
                .compile("^([a-zA-Z0-9_]+)(?:\\(([a-zA-Z0-9_]+(?:,[a-zA-Z0-9_]+)*)\\))?$");
        final Matcher matcher = pattern.matcher(str.replaceAll(" ", ""));

        if (!matcher.matches()) {
            throw new IllegalArgumentException();
        }

        return new PredicateDeclaration(matcher.group(1),
                matcher.group(2) == null ? Collections.emptyList()
                        : Arrays.asList(matcher.group(2).split(",")));
    }

    @Override
    public String toString() {
        if (argSorts.isEmpty()) {
            return predName;
        }

        return String.format("%s(%s)", predName,
                argSorts.stream().collect(Collectors.joining(", ")));
    }
}