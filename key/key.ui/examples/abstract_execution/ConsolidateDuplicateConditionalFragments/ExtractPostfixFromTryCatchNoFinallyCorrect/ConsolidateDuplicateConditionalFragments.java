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
 * A model of the "consolidate duplicate conditional fragments" refactoring by
 * M. Fowler. In this variant, a postfix is pulled out of a try-catch block and
 * put after the block. From Fowler's descriptions, it it not clear whether
 * "move it [Postfix] to the final block" refers to the "finally" block or is
 * just another way to describe moving it after the try-catch. If "finally" was
 * the intended meaning, interestingly that actually complicates the
 * refactoring, finally blocks are even executed after returns.
 * 
 * <p>
 * Discovered: We have to forbid Postfix to throw an exception; otherwise, the
 * additional effects of CatchProg prevent closing the goal.
 * 
 * <p>
 * The assumption that TryProg does not change the heap is only needed for
 * proving well-formedness of the heap etc. after "application" of the assume
 * statements in the catch clauses, which are realized as Block Contracts.
 * Alternatively, we could get that assumptions from elsewhere, like from the AE
 * rules. It would anyway make sense that legal instantiations leave the heap
 * well-formed. Disjointness from "this" should be natural, we need it for the
 * same proof obligations for technical reasons.
 *
 * @author Dominic Steinhoefel
 */
public class ConsolidateDuplicateConditionalFragments {
    //@ declares \dl_args;
    public Object before(Object res) {
        /*@ assume \disjoint(\dl_heap, \dl_frameTryProg) &&
          @        \disjoint(this, \dl_frameTryProg);
          @*/
        { ; }
        
        try {
            //@ assignable \dl_frameTryProg;
            //@ accessible \dl_footprintTryProg;
            \abstract_statement TryProg;
            
            //@ assignable \dl_framePostfixProg;
            //@ accessible \dl_footprintPostfixProg;
            //@ exceptional_behavior requires false;
            \abstract_statement Postfix;
        }
        catch (Throwable t) {
            /*@ assume \disjoint(t, \dl_footprintCatchProg) &&
              @        \disjoint(t, \dl_footprintPostfixProg);
              @*/
            { ; }
            
            //@ assignable \dl_frameCatchProg;
            //@ accessible t, \dl_footprintCatchProg;
            \abstract_statement CatchProg;

            //@ assignable \dl_framePostfixProg;
            //@ accessible \dl_footprintPostfixProg;
            //@ exceptional_behavior requires false;
            \abstract_statement Postfix;
        }

        return res;
    }

    //@ declares \dl_args;
    public Object after(Object res) {
        /*@ assume \disjoint(\dl_heap, \dl_frameTryProg) &&
          @        \disjoint(this, \dl_frameTryProg);
          @*/
        { ; }
        
        try {
            //@ assignable \dl_frameTryProg;
            //@ accessible \dl_footprintTryProg;
            \abstract_statement TryProg;
        }
        catch (Throwable t) {
            /*@ assume \disjoint(t, \dl_footprintCatchProg) &&
              @        \disjoint(t, \dl_footprintPostfixProg);
              @*/
            { ; }
            
            //@ assignable \dl_frameCatchProg;
            //@ accessible t, \dl_footprintCatchProg;
            \abstract_statement CatchProg;
        }

        //@ assignable \dl_framePostfixProg;
        //@ accessible \dl_footprintPostfixProg;
        //@ exceptional_behavior requires false;
        \abstract_statement Postfix;

        return res;
    }
}