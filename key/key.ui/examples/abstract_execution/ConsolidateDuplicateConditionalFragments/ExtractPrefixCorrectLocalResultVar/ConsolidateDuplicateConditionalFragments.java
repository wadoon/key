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
 * the additional specifications, since P might access the variable b.
 * 
 * <p>
 * P either hasTo set res, or must not do so. Having it as maybe does not work.
 * Note that since both directions work, maybe also works theoretically, but we
 * don't have proof rules for such case distinctions (currently).
 *
 * @author Dominic Steinhoefel
 */
public class ConsolidateDuplicateConditionalFragments {
    public int before() {
        Object res = null;
        
        /*@ assume \disjoint(\dl_frameE, \dl_footprintP) &&
          @        \disjoint(\dl_frameP, \dl_footprintE) &&
          @        \disjoint(\dl_frameP, \dl_frameE) &&
          @        \disjoint(\dl_frameE, res) &&
          @        \disjoint(\dl_footprintE, res) &&
          @        \disjoint(\dl_footprintP, res) &&
          @        \disjoint(\dl_footprintQ1, res) &&
          @        \disjoint(\dl_footprintQ2, res);
          @*/
        { ; }
        
        if (
            //@ assignable \dl_frameE;
            //@ accessible \dl_footprintE;
            //@ exceptional_behavior requires false;
            \abstract_expression e
        ) {
            //@ assignable \dl_frameP, \hasTo(res);
            //@ accessible \dl_footprintP;
            \abstract_statement P;
            
            //@ assignable \dl_frameQ1, \dl_hasTo(res);
            //@ accessible \dl_footprintQ1, res;
            \abstract_statement Q1;
        }
        else {
            //@ assignable \dl_frameP, \hasTo(res);
            //@ accessible \dl_footprintP;
            \abstract_statement P;
            
            //@ assignable \dl_frameQ2, \dl_hasTo(res);
            //@ accessible \dl_footprintQ2, res;
            \abstract_statement Q2;
        }

        return res;
    }

    public int after() {
        Object res = null;
        
        /*@ assume \disjoint(\dl_frameE, \dl_footprintP) &&
          @        \disjoint(\dl_frameP, \dl_footprintE) &&
          @        \disjoint(\dl_frameP, \dl_frameE) &&
          @        \disjoint(\dl_frameE, res) &&
          @        \disjoint(\dl_footprintE, res) &&
          @        \disjoint(\dl_footprintP, res) &&
          @        \disjoint(\dl_footprintQ1, res) &&
          @        \disjoint(\dl_footprintQ2, res);
          @*/
        { ; }
      
        //@ assignable \dl_frameP, \hasTo(res);
        //@ accessible \dl_footprintP;
        \abstract_statement P;
        
        if (
            //@ assignable \dl_frameE;
            //@ accessible \dl_footprintE;
            //@ exceptional_behavior requires false;
            \abstract_expression e
        ) {
            //@ assignable \dl_frameQ1, \dl_hasTo(res);
            //@ accessible \dl_footprintQ1, res;
            \abstract_statement Q1;
        }
        else {
            //@ assignable \dl_frameQ2, \dl_hasTo(res);
            //@ accessible \dl_footprintQ2, res;
            \abstract_statement Q2;
        }

        return res;
    }
}