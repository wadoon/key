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
package de.uka.ilkd.key.abstractexecution.relational.model;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlID;
import javax.xml.bind.annotation.XmlRootElement;
import javax.xml.bind.annotation.XmlTransient;

/**
 * @author Dominic Steinhoefel
 */
@XmlRootElement(name="programVariable")
public class ProgramVariableDeclaration extends NullarySymbolDeclaration {
    public static final ProgramVariableDeclaration EMPTY_DECL = //
            new ProgramVariableDeclaration("", "");

    private String typeName = "";
    private String varName = "";

    ProgramVariableDeclaration() {
    }

    public ProgramVariableDeclaration(String typeName, String varName) {
        this.typeName = typeName;
        this.varName = varName;
    }

    @XmlAttribute
    public String getTypeName() {
        return typeName;
    }

    @XmlAttribute
    @XmlID
    public String getVarName() {
        return varName;
    }

    public void setTypeName(String typeName) {
        this.typeName = typeName;
    }

    public void setVarName(String varName) {
        this.varName = varName;
    }
    
    @XmlTransient
    @Override
    public String getName() {
        return varName;
    }

    public static ProgramVariableDeclaration fromString(final String str)
            throws IllegalArgumentException {
        final Pattern pattern = Pattern.compile("^([a-zA-Z0-9_.]+) +([a-zA-Z0-9_]+)$");
        final Matcher matcher = pattern.matcher(str.trim());

        if (!matcher.matches()) {
            throw new IllegalArgumentException();
        }

        return new ProgramVariableDeclaration(matcher.group(1), matcher.group(2));
    }

    @Override
    public String toString() {
        return typeName.isEmpty() && varName.isEmpty() ? ""
                : String.format("%s %s", typeName, varName);
    }
}