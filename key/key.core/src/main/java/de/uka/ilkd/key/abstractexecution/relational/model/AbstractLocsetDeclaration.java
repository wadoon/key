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
@XmlRootElement(name="locationSet")
public class AbstractLocsetDeclaration extends NullarySymbolDeclaration {
    public static final AbstractLocsetDeclaration EMPTY_DECL = //
            new AbstractLocsetDeclaration("");

    private String locsetName = "";

    AbstractLocsetDeclaration() {
    }

    public AbstractLocsetDeclaration(String locsetName) {
        this.locsetName = locsetName;
    }

    @XmlAttribute
    @XmlID
    public String getLocsetName() {
        return locsetName;
    }

    public void setLocsetName(String typeName) {
        this.locsetName = typeName;
    }
    
    @XmlTransient
    @Override
    public String getName() {
        return locsetName;
    }

    public static AbstractLocsetDeclaration fromString(final String str)
            throws IllegalArgumentException {
        final Pattern pattern = Pattern.compile("^([a-zA-Z0-9_.]+)$");
        final Matcher matcher = pattern.matcher(str.trim());

        if (!matcher.matches()) {
            throw new IllegalArgumentException();
        }

        return new AbstractLocsetDeclaration(matcher.group(1));
    }

    @Override
    public String toString() {
        return locsetName;
    }
}