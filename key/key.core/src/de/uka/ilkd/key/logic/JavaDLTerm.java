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

package de.uka.ilkd.key.logic;

import org.key_project.common.core.logic.GenericTerm;
import org.key_project.util.collection.ImmutableArray;

/**
 * {@link GenericTerm} extension for Java terms, provides methods related to
 * contained Java statements.
 *
 * @author Dominic Scheurer
 */
public interface JavaDLTerm extends GenericTerm<JavaDLVisitor> {

    @Override
    public ImmutableArray<JavaDLTerm> subs();

    @Override
    public JavaDLTerm sub(int nr);

    /**
     * The Java block at top level.
     */
    @Override
    public JavaBlock modalContent();

    @Override
    void execPostOrder(JavaDLVisitor visitor);

}
