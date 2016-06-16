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

package org.key_project.common.core.rule;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.Named;

/** 
 * Represents a taclet option. A taclet option consists of
 * a category and an option name. For instance, <code>programRules:Java</code>
 * is a taclet option with category <code>programRules</code> and option name <code>Java</code>
 */
public class TacletOption implements Named {

    private final Name name;
    private final String category;

    /** 
     * creates a taclet option with name {@code <category>:<name>}.
     */
    public TacletOption(String name, String category){
	this(new Name(category + ":" + name), category);
    }
    

    public TacletOption(Name name, String category){
	this.name = name;
	// .intern() crucial for correct equals
	this.category = category.intern();       
    }

    
    @Override
    public Name name(){
	return name;
    }

    public String category(){
	return category;
    }

    
    @Override
    public boolean equals(Object o) {
	if (!(o instanceof TacletOption)) {
	    return false;
	}
	final TacletOption c = (TacletOption)o;
	return category == c.category && name.equals(c.name);
	    
    }
    
    @Override
    public int hashCode() {
	return name.hashCode()*37;
    }


    @Override
    public String toString(){
	return name.toString();
    }
}