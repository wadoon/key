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

package de.uka.ilkd.key.java;

import org.key_project.common.core.services.TermServices;

import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.JavaDLVisitor;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public interface JavaDLTermServices
        extends
        TermServices<SourceElement, JavaDLTerm, JavaDLVisitor, NameAbstractionTable, JavaBlock> {

}
