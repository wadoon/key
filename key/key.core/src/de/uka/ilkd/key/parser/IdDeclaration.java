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

package de.uka.ilkd.key.parser;

public class IdDeclaration {

    private String name;
    private org.key_project.common.core.logic.Sort   sort;

    public IdDeclaration ( String p_name,
			   org.key_project.common.core.logic.Sort   p_sort ) {
	name = p_name;
	sort = p_sort;
    }

    public String getName () {
	return name;
    }

    public org.key_project.common.core.logic.Sort   getSort () {
	return sort;
    }

}