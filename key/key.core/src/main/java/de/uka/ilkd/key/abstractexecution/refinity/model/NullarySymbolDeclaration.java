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

import javax.xml.bind.annotation.XmlTransient;

/**
 * @author Dominic Steinhoefel
 */
public abstract class NullarySymbolDeclaration {
    private int relevantOne = -1;
    private int relevantTwo = -1;
    
    /**
     * @return The name of this {@link NullarySymbolDeclaration} for displaying it
     *         in the GUI.
     */
    @XmlTransient
    public abstract String getName();
    
    public abstract String toSeqSingleton();

    /**
     * @return -1 if this {@link NullarySymbolDeclaration} is not relevant for the
     *         left program or otherwise the position of this symbol within the list
     *         of relevant symbols for the left program.
     */
    public int getRelevantOne() {
        return relevantOne;
    }

    /**
     * @param pos -1 if this {@link NullarySymbolDeclaration} is not relevant for
     *            the left program or otherwise the position of this symbol within
     *            the list of relevant symbols for the left program.
     */
    public void setRelevantOne(int pos) {
        this.relevantOne = pos;
    }

    /**
     * @return -1 if this {@link NullarySymbolDeclaration} is not relevant for the
     *         right program or otherwise the position of this symbol within the
     *         list of relevant symbols for the right program.
     */
    public int getRelevantTwo() {
        return relevantTwo;
    }

    /**
     * @param pos -1 if this {@link NullarySymbolDeclaration} is not relevant for
     *            the right program or otherwise the position of this symbol within
     *            the list of relevant symbols for the right program.
     */
    public void setRelevantTwo(int pos) {
        this.relevantTwo = pos;
    }
}
