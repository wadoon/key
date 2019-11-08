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
 * <p>
 * Additionally, this version allows the guard and the extracted fragment to
 * complete abruptly; but if the guard completes abruptly, the fragment may not
 * do so, and vice versa.
 * 
 * <p>
 * Note that the refactoring is *not* correct if the frame of the extracted
 * fragment is relevant for the result. In this case, it may have changed something
 * before the expression terminates abruptly, leading to different results!
 *
 * @author Dominic Steinhoefel
 */
public class ConsolidateDuplicateConditionalFragments {
    public Object before(Object result) {
        /*@ assume \disjoint(\dl_frameE, \dl_footprintP) &&
          @        \disjoint(\dl_frameP, \dl_footprintE) &&
          @        \disjoint(\dl_frameP, \dl_frameE) &&
          @        \disjoint(\dl_frameE, \dl_relevant) &&
          @        \disjoint(\dl_frameP, \dl_relevant) &&
          @        \dl_mutex3(\dl_throwsExcE(\dl_value(\dl_footprintE)),
          @                   \dl_throwsExcP(\dl_value(\dl_footprintP)),
          @                   \dl_returnsP(\dl_value(\dl_footprintP)));
          @*/
        { ; }
        
        if (
            /*@ assignable \dl_frameE;
              @ accessible \dl_footprintE;
              @ exceptional_behavior requires \dl_throwsExcE(\dl_value(\dl_footprintE));
              @*/
            \abstract_expression boolean e
        ) {
            /*@ assignable \dl_frameP;
              @ accessible \dl_footprintP;
              @ exceptional_behavior requires \dl_throwsExcP(\dl_value(\dl_footprintP));
              @ return_behavior requires \dl_returnsP(\dl_value(\dl_footprintP));
              @*/
            \abstract_statement P;
            
            //@ assignable \dl_frameQ1;
            //@ accessible \dl_footprintQ1;
            //@ exceptional_behavior signals (Throwable t) t != null;
            \abstract_statement Q1;
        }
        else {
            /*@ assignable \dl_frameP;
              @ accessible \dl_footprintP;
              @ exceptional_behavior requires \dl_throwsExcP(\dl_value(\dl_footprintP));
              @ return_behavior requires \dl_returnsP(\dl_value(\dl_footprintP));
              @*/
            \abstract_statement P;
            
            //@ assignable \dl_frameQ2;
            //@ accessible \dl_footprintQ2;
            //@ exceptional_behavior signals (Throwable t) t != null;
            \abstract_statement Q2;
        }

        return result;
    }

    public Object after(Object result) {
        /*@ assume \disjoint(\dl_frameE, \dl_footprintP) &&
          @        \disjoint(\dl_frameP, \dl_footprintE) &&
          @        \disjoint(\dl_frameP, \dl_frameE) &&
          @        \disjoint(\dl_frameE, \dl_relevant) &&
          @        \disjoint(\dl_frameP, \dl_relevant) &&
          @        \dl_mutex3(\dl_throwsExcE(\dl_value(\dl_footprintE)),
          @                   \dl_throwsExcP(\dl_value(\dl_footprintP)),
          @                   \dl_returnsP(\dl_value(\dl_footprintP)));
          @*/
        { ; }

        /*@ assignable \dl_frameP;
          @ accessible \dl_footprintP;
          @ exceptional_behavior requires \dl_throwsExcP(\dl_value(\dl_footprintP));
          @ return_behavior requires \dl_returnsP(\dl_value(\dl_footprintP));
          @*/
        \abstract_statement P;
        
        if (
            /*@ assignable \dl_frameE;
              @ accessible \dl_footprintE;
              @ exceptional_behavior requires \dl_throwsExcE(\dl_value(\dl_footprintE));
              @*/
            \abstract_expression boolean e
        ) {
            //@ assignable \dl_frameQ1;
            //@ accessible \dl_footprintQ1;
            //@ exceptional_behavior signals (Throwable t) t != null;
            \abstract_statement Q1;
        }
        else {
            //@ assignable \dl_frameQ2;
            //@ accessible \dl_footprintQ2;
            //@ exceptional_behavior signals (Throwable t) t != null;
            \abstract_statement Q2;
        }

        return result;
    }
}