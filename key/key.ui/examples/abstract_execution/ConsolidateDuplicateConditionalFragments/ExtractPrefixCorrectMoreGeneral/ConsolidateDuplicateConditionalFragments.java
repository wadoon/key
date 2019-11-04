// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

/**
 * A model of a variant of the "consolidate duplicate conditional fragments"
 * refactoring by M. Fowler. Note that this refactoring is *not* correct without
 * the additional specifications, since P might access the if guard (AExp e).
 *
 * @author Dominic Steinhoefel
 */
public class ConsolidateDuplicateConditionalFragments {
    public Object before(Object result) {
        /*@ assume \disjoint(\dl_frameE, \dl_footprintP) &&
          @        \disjoint(\dl_frameP, \dl_footprintE) &&
          @        \disjoint(\dl_frameP, \dl_frameE) &&
          @        \disjoint(\dl_frameE, \dl_relevant);
          @*/
        { ; }
        
        if (
            //@ assignable \dl_frameE;
            //@ accessible \dl_footprintE;
            //@ exceptional_behavior requires false;
            \abstract_expression boolean e
        ) {
            //@ assignable \dl_frameP;
            //@ accessible \dl_footprintP;
            \abstract_statement P;
            
            //@ assignable \dl_frameQ1;
            //@ accessible \dl_footprintQ1;
            \abstract_statement Q1;
        }
        else {
            //@ assignable \dl_frameP;
            //@ accessible \dl_footprintP;
            \abstract_statement P;
            
            //@ assignable \dl_frameQ2;
            //@ accessible \dl_footprintQ2;
            \abstract_statement Q2;
        }

        return result;
    }

    public Object after(Object result) {
        /*@ assume \disjoint(\dl_frameE, \dl_footprintP) &&
          @        \disjoint(\dl_frameP, \dl_footprintE) &&
          @        \disjoint(\dl_frameP, \dl_frameE) &&
          @        \disjoint(\dl_frameE, \dl_relevant);
          @*/
        { ; }
      
        //@ assignable \dl_frameP;
        //@ accessible \dl_footprintP;
        \abstract_statement P;
        
        if (
            //@ assignable \dl_frameE;
            //@ accessible \dl_footprintE;
            //@ exceptional_behavior requires false;
            \abstract_expression boolean e
        ) {
            //@ assignable \dl_frameQ1;
            //@ accessible \dl_footprintQ1;
            \abstract_statement Q1;
        }
        else {
            //@ assignable \dl_frameQ2;
            //@ accessible \dl_footprintQ2;
            \abstract_statement Q2;
        }

        return result;
    }
}