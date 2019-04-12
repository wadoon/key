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
 * put into the finally block.
 * 
 * Discovered: TryProg and CatchProg may not return, since after the
 * refactoring, the finally block will be executed even after the return
 * statement, alternating the behavior. For the same reason, CatchProg may not
 * throw an exception.
 *
 * @author Dominic Steinhoefel
 */
public class ConsolidateDuplicateConditionalFragments {
    public Object before(Object result) {
        try {
            //@ return_behavior requires false;
            { \abstract_statement TryProg; }
            
            \abstract_statement Postfix;
        }
        catch (Throwable t) {
            //@ exceptional_behavior requires false;
            //@ return_behavior requires false;
            { \abstract_statement CatchProg; }
            
            \abstract_statement Postfix;
        }

        return result;
    }

    public Object after(Object result) {
        try {
            //@ return_behavior requires false;
            { \abstract_statement TryProg; }
        }
        catch (Throwable t) {
            //@ exceptional_behavior requires false;
            //@ return_behavior requires false;
            { \abstract_statement CatchProg; }
        } finally {
            \abstract_statement Postfix;
        }

        return result;
    }
}