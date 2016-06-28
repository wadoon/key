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

package org.key_project.bytecode.core.logic.op;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.op.CCProgramVariable;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.program.abstraction.SortedType;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
public abstract class ProgramVariable extends CCProgramVariable {
    
    private final boolean isFinal;
    private final boolean isStatic;

    /**
     * TODO: Document.
     *
     * @param name
     * @param s
     * @param t
     * @param isModel
     * @param isGhost
     */
    protected ProgramVariable(Name name, Sort s, SortedType t, boolean isModel,
            boolean isGhost) {
        this(name, s, t, isModel, isGhost, false, false);
    }

    /**
     * TODO: Document.
    *
    * @param name
    * @param s
    * @param t
    * @param isModel
    * @param isGhost
    */
   protected ProgramVariable(Name name, Sort s, SortedType t, boolean isModel,
           boolean isGhost, boolean isFinal, boolean isStatic) {
       super(name, s, t, isModel, isGhost);
       this.isFinal = isFinal;
       this.isStatic = isStatic;
   }
   
   /**
    * @return the isFinal
    */
   public boolean isFinal() {
       return isFinal;
   }

   /**
    * @return the isStatic
    */
   public boolean isStatic() {
       return isStatic;
   }

}
