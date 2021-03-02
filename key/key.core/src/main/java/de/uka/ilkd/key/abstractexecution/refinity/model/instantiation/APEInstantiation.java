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
public class APEInstantiation {
    @XmlAttribute(name = "apeLineNumber")
    private int apeLineNumber = -1;
    @XmlElement(name = "instantiation")
    private String instantiation;

    public APEInstantiation() {
    }

    public APEInstantiation(final int apeLineNumber, final String instantiation) {
        this.apeLineNumber = apeLineNumber;
        this.instantiation = instantiation;
    }

    public int getApeLineNumber() {
        return apeLineNumber;
    }

    public void setApeLineNumber(int apeLineNumber) {
        this.apeLineNumber = apeLineNumber;
    }

    public String getInstantiation() {
        return instantiation;
    }

    public void setInstantiation(String instantiation) {
        this.instantiation = instantiation;
    }

    @Override
    public String toString() {
        assert apeLineNumber >= 0;
        assert instantiation != null;

        return String.format("APE @ line %d: \"%s\"", apeLineNumber, instantiation);
    }

    @Override
    public boolean equals(Object obj) {
        return obj != null && (obj instanceof APEInstantiation)
                && ((APEInstantiation) obj).apeLineNumber == this.apeLineNumber
                && ((APEInstantiation) obj).instantiation.equals(this.instantiation);
    }

}
