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

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;

/**
 * @author Dominic Steinhoefel
 */
@XmlRootElement
@XmlAccessorType(XmlAccessType.FIELD)
public class MethodDeclaration {
    @XmlElement(name = "name")
    private String name;

    @XmlElement(name = "body")
    private String methodBody;

    public MethodDeclaration(final String name, final String methodBody) {
        this.name = name;
        this.methodBody = methodBody;
    }

    MethodDeclaration() {
    }

    public String getName() {
        return name;
    }

    public void setName(final String name) {
        this.name = name;
    }

    public String getMethodBody() {
        return methodBody;
    }

    public void setMethodBody(final String methodBody) {
        this.methodBody = methodBody;
    }

    @Override
    public String toString() {
        return name;
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof MethodDeclaration && obj != null
                && name.equals(((MethodDeclaration) obj).name)
                && methodBody.equals(((MethodDeclaration) obj).methodBody);
    }
    
    @Override
    public int hashCode() {
        return 3 * name.hashCode() + 17 * methodBody.hashCode();
    }
}
