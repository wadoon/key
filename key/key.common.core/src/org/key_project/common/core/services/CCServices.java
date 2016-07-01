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

package org.key_project.common.core.services;

import org.key_project.common.core.logic.CCTerm;
import org.key_project.common.core.logic.ModalContent;
import org.key_project.common.core.logic.factories.CCTermBuilder;
import org.key_project.common.core.logic.factories.CCTermFactory;

/**
 * The general services interface provides access to all important sub-services.
 *
 * @author Dominic Scheurer
 */
public interface CCServices<P extends ModalContent<?>, T extends CCTerm<?, P, ?, T>, TB extends CCTermBuilder<P, T>, TF extends CCTermFactory<P, T>>
        extends TermServices<P, T, TB, TF>,
        CCProofServices {

}
