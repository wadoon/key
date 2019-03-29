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
 * @author Dominic Steinhoefel
 */
public class ConsolidateDuplicateConditionalFragments {
    public int before(Object result, boolean b) {
        if (b) {
            //@ assignable \dl_heap, \dl_localsP, result;
            //@ accessible \dl_heap, \dl_localsP, result;
            //@ declares \dl_localsP;
            { abstract_statement P; }
            abstract_statement Q1;
        }
        else {
            //@ assignable \dl_heap, \dl_localsP, result;
            //@ accessible \dl_heap, \dl_localsP, result;
            //@ declares \dl_localsP;
            { abstract_statement P; }
            abstract_statement Q2;
        }

        return result;
    }

    public int after(Object result, boolean b) {
        //@ assignable \dl_heap, \dl_localsP, result;
        //@ accessible \dl_heap, \dl_localsP, result;
        //@ declares \dl_localsP;
        { abstract_statement P; }
        
        if (b) {
            abstract_statement Q1;
        }
        else {
            abstract_statement Q2;
        }

        return result;
    }
}