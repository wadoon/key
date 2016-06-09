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

import org.key_project.common.core.logic.op.SchemaVariable;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.JavaDLTerm;

public class Trigger {

    /** trigger related information */
    private final JavaDLTerm trigger;
    private final ImmutableList<JavaDLTerm> avoidConditions;
    private final SchemaVariable triggerVar;
    
    
    public Trigger(SchemaVariable triggerVar, JavaDLTerm trigger,  
            ImmutableList<JavaDLTerm> avoidConditions) {
        assert triggerVar != null;
        assert trigger != null;
        assert avoidConditions != null;
        
        this.triggerVar = triggerVar;
        this.trigger = trigger;
        this.avoidConditions = avoidConditions;
    }


    public SchemaVariable getTriggerVar() {
        return triggerVar;
    }

    public JavaDLTerm getTerm() {
        return trigger;
    }

    public ImmutableList<JavaDLTerm> getAvoidConditions() {
        return avoidConditions;
    }

    public boolean hasAvoidConditions() {
        return !avoidConditions.isEmpty();
    }
    
}