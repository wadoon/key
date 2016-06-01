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

package de.uka.ilkd.key.rule;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.Named;

import de.uka.ilkd.key.util.Pair;

public class Choice extends Pair<Name, String> implements Named {

    /** 
     * creates a choice object with name <category>:<choice>.
     */
    public Choice(String choice, String category){
	this(new Name(category + ":" + choice), category);
    }
    

    public Choice(Name name, String category){
        super(name, category);
    }

    
    @Override
    public Name name(){
        return first;
    }

    public String category(){
        return second;
    }


    @Override
    public String toString(){
        return first.toString();
    }
}