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

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlID;
import javax.xml.bind.annotation.XmlRootElement;
import javax.xml.bind.annotation.XmlTransient;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.Function;

/**
 * @author Dominic Steinhoefel
 */
@XmlRootElement(name = "locationSet")
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

    @Override
    public String toSeqSingleton() {
        return String.format("seqSingleton(value(%s))", locsetName);
    }

    /**
     * Adds a function symbol corresponding to this
     * {@link AbstractLocsetDeclaration} to the {@link Services} object if not
     * already present.
     * 
     * @param services The {@link Services} object whose namespaces to populate.
     * @throws RuntimeException If the name is already present.
     */
    public void checkAndRegister(final Services services) {
        final NamespaceSet namespaces = services.getNamespaces();
        if (namespaces.functions().lookup(getLocsetName()) != null) {
            throw new RuntimeException(
                    "The name " + this + " is already registered, please choose another one.",
                    null);
        }

        namespaces.functions().add(new Function(new Name(getLocsetName()),
                services.getTypeConverter().getLocSetLDT().targetSort()));
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

    @Override
    public boolean equals(Object obj) {
        return obj instanceof AbstractLocsetDeclaration && obj != null
                && ((AbstractLocsetDeclaration) obj).locsetName.equals(locsetName);
    }
}