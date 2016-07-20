// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import org.key_project.common.core.logic.op.CCSchemaVariableFactory;

import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;

/**
 * A factory class for different Schema Variables
 */
public class SchemaVariableFactory extends CCSchemaVariableFactory {

    private SchemaVariableFactory() {
    }

    /**
     * creates a SchemaVariable representing a program construct
     */
    public static ProgramSV createProgramSV(ProgramElementName name,
            ProgramSVSort s,
            boolean listSV) {
        return new ProgramSV(name, s, listSV);
    }
}