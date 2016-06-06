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

package org.key_project.common.core.logic.sort;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.Named;
import org.key_project.common.core.logic.op.SortDependingFunction;
import org.key_project.common.core.services.GenericProofServices;
import org.key_project.common.core.services.TermServices;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;


public interface Sort extends Named {
    
    static class SpecialSort implements Sort {

        private final Name name;

        public SpecialSort(Name name) {
            this.name = name;
        }
        
        @Override
        public Name name() {
           return name;
        }

        @Override
        public ImmutableSet<Sort> extendsSorts() {
            return DefaultImmutableSet.<Sort>nil();
        }

        @Override
        public ImmutableSet<Sort> extendsSorts(GenericProofServices services) {
            return extendsSorts();
        }

        @Override
        public boolean extendsTrans(Sort s) {
            return s == this;
        }

        @Override
        public boolean isAbstract() {
            return false;
        }

        @Override
        public SortDependingFunction getCastSymbol(TermServices services) {
            throw new UnsupportedOperationException("Cannot cast to " + name);
        }

        @Override
        public SortDependingFunction getInstanceofSymbol(
                TermServices services) {
            throw new UnsupportedOperationException("Cannot check instanceof for " + name);
        }

        @Override
        public SortDependingFunction getExactInstanceofSymbol(
                TermServices services) {
            throw new UnsupportedOperationException("Cannot check exactInstanceof for " + name);
        }

        @Override
        public String declarationString() {
            return name.toString();
        }
        
    }
    
    /**
     * Formulas are represented as "terms" of this sort.
     */
    final Sort FORMULA = new SpecialSort(new Name("Formula"));
    
    /**
     * Updates are represented as "terms" of this sort.
     */
    final Sort UPDATE = new SpecialSort(new Name("Update"));

    /**
     * Term labels are represented as "terms" of this sort.
     */
    final Sort TERMLABEL = new SpecialSort(new Name("TermLabel"));

    public final Name CAST_NAME = new Name("cast");
    final Name INSTANCE_NAME = new Name("instance");
    final Name EXACT_INSTANCE_NAME = new Name("exactInstance");    
    
    
    /**
     * Returns the direct supersorts of this sort. Not supported by NullSort.
     */
    ImmutableSet<Sort> extendsSorts();
    
    /**
     * Returns the direct supersorts of this sort.
     */
    <T extends GenericProofServices> ImmutableSet<Sort> extendsSorts(T services); 

    /**
     * Tells whether the given sort is a reflexive, transitive subsort of this 
     * sort.
     */
    boolean extendsTrans(Sort s);
    
    /**
     * Tells whether this sort has no exact elements.
     */
    boolean isAbstract();
    
    /**
     * returns the cast symbol of this Sort
     */
    SortDependingFunction getCastSymbol(TermServices services);
    
    /**
     * returns the instanceof symbol of this Sort
     */
    SortDependingFunction getInstanceofSymbol(TermServices services);
    
    /**
     * returns the exactinstanceof symbol of this Sort
     */
    SortDependingFunction getExactInstanceofSymbol(TermServices services);

    String declarationString();
}
