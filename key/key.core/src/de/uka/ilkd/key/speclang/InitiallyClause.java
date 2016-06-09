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

package de.uka.ilkd.key.speclang;

import org.key_project.common.core.logic.op.ParsableVariable;
import org.key_project.common.core.services.TermServices;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JavaDLTerm;


public interface InitiallyClause extends SpecificationElement {
     

    
    
    /**
     * Returns the formula without implicit all-quantification over
     * the receiver object.
     */
    public JavaDLTerm getClause(ParsableVariable selfVar, TermServices services);
    
    public PositionedString getOriginalSpec();
    
    public InitiallyClause setKJT(KeYJavaType newKjt);

  
}