// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.model.instantiation;

import java.util.stream.Collectors;
import java.util.stream.IntStream;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;

import de.uka.ilkd.key.abstractexecution.refinity.model.PredicateDeclaration;

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
    
    public PredicateInstantiation() {
    }

    public PredicateInstantiation(final PredicateDeclaration declaration,
            final String instantiation) {
        this.declaration = declaration;
        this.instantiation = instantiation;
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

    @Override
    public String toString() {
        assert declaration != null;
        assert instantiation != null;
        
        final String paramDecl = IntStream.range(1, declaration.getArgSorts().size()).mapToObj(
                i -> String.format("(\\forall %s _p%d; ", declaration.getArgSorts().get(i - 1), i))
                .collect(Collectors.joining());

        final String closingParens = IntStream.range(1, declaration.getArgSorts().size())
                .mapToObj(i -> ")").collect(Collectors.joining());

        return paramDecl + instantiation + closingParens;
    }

    @Override
    public boolean equals(Object obj) {
        return obj != null && (obj instanceof PredicateInstantiation)
                && ((PredicateInstantiation) obj).declaration.equals(this.declaration)
                && ((PredicateInstantiation) obj).instantiation.equals(this.instantiation);
    }

}
