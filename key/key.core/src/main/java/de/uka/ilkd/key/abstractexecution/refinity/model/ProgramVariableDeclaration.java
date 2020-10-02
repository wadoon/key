// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.model;

import java.util.Optional;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlID;
import javax.xml.bind.annotation.XmlRootElement;
import javax.xml.bind.annotation.XmlTransient;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariableBuilder;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * @author Dominic Steinhoefel
 */
@XmlRootElement(name = "programVariable")
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

    @Override
    public String toSeqSingleton() {
        return String.format("seqSingleton(value(singletonPV(%s)))", varName);
    }

    /**
     * Adds a program variable symbol corresponding to this
     * {@link ProgramVariableDeclaration} to the {@link Services} object if not
     * already present.
     * 
     * @param services The {@link Services} object whose namespaces to populate.
     */
    public void checkAndRegisterSave(final Services services) {
        final Sort sort = services.getNamespaces().sorts().lookup(getTypeName());

        if (sort == null) {
            throw new RuntimeException("Sort \"" + getTypeName() + "\" is not known");
        }

        final Name name = new Name(getVarName());

        if (services.getNamespaces().lookup(name) != null) {
            throw new RuntimeException("The name \"" + getVarName()
                    + "\" is already known to the system.<br/>\n" + "Plase choose a fresh one.");
        }

        services.getNamespaces().programVariables().add(new LocationVariableBuilder(
                new ProgramElementName(getVarName()), services.getJavaInfo().getKeYJavaType(sort)).create());
    }

    /**
     * Adds a program variable symbol corresponding to this
     * {@link ProgramVariableDeclaration} to the {@link Services} object
     * 
     * @param services The {@link Services} object whose namespaces to populate.
     * @return true iff successful.
     */
    public boolean registerIfUnknown(final Services services) {
        final Sort sort = services.getNamespaces().sorts().lookup(getTypeName());

        if (sort == null) {
            throw new RuntimeException("Sort \"" + getTypeName() + "\" is not known");
        }

        final Name name = new Name(getVarName());

        if (services.getNamespaces().lookup(name) == null) {
            services.getNamespaces().programVariables()
                    .add(new LocationVariableBuilder(new ProgramElementName(getVarName()),
                            services.getJavaInfo().getKeYJavaType(sort)).create());
            return true;
        }

        return false;
    }

    public static Optional<ProgramVariableDeclaration> fromString(final String str)
            throws IllegalArgumentException {
        final Pattern pattern = Pattern
                .compile("^([a-zA-Z0-9_.]+(?: *\\[\\] *)?) +([a-zA-Z0-9_]+)$");
        final Matcher matcher = pattern.matcher(str.trim());

        if (!matcher.matches()) {
            return Optional.empty();
        }

        return Optional.of(new ProgramVariableDeclaration(matcher.group(1).replace(" ", ""),
                matcher.group(2)));
    }

    public String toKeYFileDecl() {
        return String.format("%s %s;", getTypeName(), getVarName());
    }

    @Override
    public String toString() {
        return typeName.isEmpty() && varName.isEmpty() ? ""
                : String.format("%s %s", typeName, varName);
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof ProgramVariableDeclaration && obj != null
                && ((ProgramVariableDeclaration) obj).typeName.equals(typeName)
                && ((ProgramVariableDeclaration) obj).varName.equals(varName);
    }
}
