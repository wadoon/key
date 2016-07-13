// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package org.key_project.bytecode.core.services;

import java.util.Collections;
import java.util.Map;

import org.key_project.bytecode.core.logic.Term;
import org.key_project.bytecode.core.theories.BytecodeTheory;
import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.services.CCTheoryServices;
import org.key_project.common.core.theories.CCIntegerTheory;
import org.key_project.common.core.theories.CCTheory;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
public class TheoryServices implements CCTheoryServices {
    // Maps LDT names to LDT instances.
    private Map<Name, CCTheory> theories;

    public TheoryServices() {
        theories = Collections.emptyMap();
    }
    
    public TheoryServices(BCTermServices services) {
        init(services);
    }

    /**
     * initializes this service by copying the content of {@code theoryServices}
     * 
     * @param theoryServices
     *            the {@link TheoryServices} to copy
     */
    void init(TheoryServices theoryServices) {
        this.theories = Collections.unmodifiableMap(theoryServices.theories);
    }

    /**
     * populates this service by fresh LDTS obtained from
     * {@link LDT#getNewLDTInstances(Services)}
     * 
     * @param theoryServices
     *            the {@link Services}
     */
    public void init(BCTermServices services) {
        theories =
                Collections.unmodifiableMap(BytecodeTheory
                        .getNewLDTInstances(services));
    }

    @Override
    public CCTheory getTheory(Name theoryName) {
        return theories.get(theoryName);
    }

    @Override
    public CCTheory getTheoryFor(Sort sort) {
        for (final CCTheory theory : theories.values()) {
            if (sort.equals(theory.targetSort())) {
                return theory;
            }
        }
        return null;
    }

    @Override
    public Iterable<? extends CCTheory> getTheories() {
        return theories.values();
    }
    
    @SuppressWarnings("unchecked")
    public CCIntegerTheory<Term> getIntegerTheory() {
        return (CCIntegerTheory<Term>) theories.get(new Name("int"));
    }

}
