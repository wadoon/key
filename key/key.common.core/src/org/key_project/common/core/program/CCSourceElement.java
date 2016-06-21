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

package org.key_project.common.core.program;

import org.key_project.common.core.logic.op.SVSubstitute;

/**
 * A source element is a piece of syntax. It does not necessarily have a
 * semantics, at least none that is machinable, for instance a comment.
 */
public interface CCSourceElement extends SVSubstitute {

}
