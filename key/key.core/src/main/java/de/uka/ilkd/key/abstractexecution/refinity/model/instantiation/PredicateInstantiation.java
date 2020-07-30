// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.model.instantiation;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;

import de.uka.ilkd.key.abstractexecution.refinity.model.FuncOrPredDecl;
import de.uka.ilkd.key.abstractexecution.refinity.model.PredicateDeclaration;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * @author Dominic Steinhoefel
 */
@XmlRootElement
@XmlAccessorType(XmlAccessType.FIELD)
public class PredicateInstantiation {
    @XmlElement(name = "declaration")
    private PredicateDeclaration declaration;
    @XmlElement(name = "instantiation")
    private String instantiation;
    @XmlElement(name = "instArgSort")
    private List<String> instArgSorts = new ArrayList<>();

    public PredicateInstantiation() {
    }

    public PredicateInstantiation(final PredicateDeclaration declaration,
            final String instantiation, final List<String> instArgSorts) {
        this.declaration = declaration;
        this.instantiation = instantiation;
        this.instArgSorts = instArgSorts;
    }

    public PredicateDeclaration getDeclaration() {
        return declaration;
    }

    public void setDeclaration(PredicateDeclaration declaration) {
        this.declaration = declaration;
    }

    public String getInstantiation() {
        return instantiation;
    }

    public void setInstantiation(String instantiation) {
        this.instantiation = instantiation;
    }

    public List<String> getInstArgSorts() {
        return instArgSorts;
    }

    public void setInstArgSorts(List<String> instArgSorts) {
        this.instArgSorts = instArgSorts;
    }

    /**
     * Adds a function symbol corresponding to this {@link FuncOrPredDecl} to the
     * {@link Services} object if not already present.
     * 
     * @param services The {@link Services} object whose namespaces to populate.
     * @throws RuntimeException If the name is already present or some sort not
     * known.
     */
    public void checkAndRegisterSave(final Services services) {
        final NamespaceSet namespaces = services.getNamespaces();

        final List<Sort> sorts = //
                getInstArgSorts().stream().map(namespaces.sorts()::lookup)
                        .collect(Collectors.toList());

        for (int i = 0; i < sorts.size(); i++) {
            if (sorts.get(i) == null) {
                throw new RuntimeException("The sort " + getInstArgSorts().get(i) + " is unknown.",
                        null);
            }
        }

        final String predName = declaration.getPredName();

        if (namespaces.functions().lookup(predName) != null) {
            throw new RuntimeException("The predicate " + predName
                    + " is already registered, please choose another one.", null);
        }

        namespaces.functions()
                .add(new Function(new Name(predName), Sort.FORMULA, sorts.toArray(new Sort[0])));
    }

    /**
     * Adds a function symbol corresponding to this {@link FuncOrPredDecl} to the
     * {@link Services} object if not already present.
     * 
     * @param services The {@link Services} object whose namespaces to populate.
     * @throws RuntimeException If some sort not known.
     * @return true iff successful.
     */
    public boolean registerIfUnknown(final Services services) {
        final NamespaceSet namespaces = services.getNamespaces();

        final List<Sort> sorts = //
                getInstArgSorts().stream().map(namespaces.sorts()::lookup)
                        .collect(Collectors.toList());

        for (int i = 0; i < sorts.size(); i++) {
            if (sorts.get(i) == null) {
                throw new RuntimeException("The sort " + getInstArgSorts().get(i) + " is unknown.",
                        null);
            }
        }

        final String predName = declaration.getPredName();

        if (namespaces.functions().lookup(predName) == null) {
            namespaces.functions().add(
                    new Function(new Name(predName), Sort.FORMULA, sorts.toArray(new Sort[0])));
            return true;
        }

        return false;
    }

    public String toDeclarationString() {
        if (instArgSorts.isEmpty()) {
            return String.format("%s;", declaration.getPredName());
        }

        return String.format("%s(%s);", declaration.getPredName(),
                instArgSorts.stream().collect(Collectors.joining(", ")));
    }

    @Override
    public String toString() {
        assert declaration != null;
        assert instantiation != null;
        assert instArgSorts != null;

        return String.format("%s -> %s", declaration, instantiation);
    }

    @Override
    public boolean equals(Object obj) {
        return obj != null && (obj instanceof PredicateInstantiation)
                && ((PredicateInstantiation) obj).declaration.equals(this.declaration)
                && ((PredicateInstantiation) obj).instantiation.equals(this.instantiation)
                && ((PredicateInstantiation) obj).instArgSorts.equals(this.instArgSorts);
    }

}
