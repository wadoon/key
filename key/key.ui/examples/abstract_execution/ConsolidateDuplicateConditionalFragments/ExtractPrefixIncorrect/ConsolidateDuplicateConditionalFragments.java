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
 * additional specifications, since P might access the variable b.
 *
 * @author Dominic Steinhoefel
 */
public class ConsolidateDuplicateConditionalFragments {
    public Object before(Object result) {
        if (
            //@ exceptional_behavior requires false;
            \abstract_expression boolean e
        ) {
            \abstract_statement P;
            \abstract_statement Q1;
        }
        else {
            \abstract_statement P;
            \abstract_statement Q2;
        }

        return result;
    }

    public Object after(Object result) {
        \abstract_statement P;

        if (
            //@ exceptional_behavior requires false;
            \abstract_expression boolean e
        ) {
            \abstract_statement Q1;
        }
        else {
            \abstract_statement Q2;
        }

        return result;
    }
}