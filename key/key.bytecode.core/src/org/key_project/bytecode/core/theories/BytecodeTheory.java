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

package org.key_project.bytecode.core.theories;

import java.util.Map;
import java.util.TreeMap;

import org.key_project.bytecode.core.logic.services.BCTermServices;
import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.theories.CCTheory;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class BytecodeTheory extends CCTheory {

    /**
     * TODO: Document.
     *
     * @param name
     * @param targetSort
     */
    protected BytecodeTheory(Name name, Sort targetSort) {
        super(name, targetSort);
    }

    /**
     * TODO: Document.
     *
     * @param name
     * @param services
     */
    protected BytecodeTheory(Name name, BCTermServices services) {
        super(name, services);
    }
    
    // -------------------------------------------------------------------------
     // public methods
     // -------------------------------------------------------------------------

    /*
     * Use this method to instantiate all LDTs. It returns a map that takes as
     * input the name of an LDT and returns an instance of the corresponding
     * LDT.
     */
    public static Map<Name, CCTheory> getNewLDTInstances(BCTermServices s) {

        // TreeMap ensures the map is sorted according
        // to the natural order of its keys.
        Map<Name, CCTheory> ret = new TreeMap<Name, CCTheory>();

        ret.put(IntegerTheory.NAME, new IntegerTheory(s));

        return ret;
    }

}
