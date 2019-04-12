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
 * M. Fowler.
 *
 * @author Dominic Steinhoefel
 */
public class ConsolidateDuplicateConditionalFragmentsPostfix {
    public int before(Object result, boolean b) {
        if (b) {
            \abstract_statement Q1;
            \abstract_statement P;
        }
        else {
            \abstract_statement Q2;
            \abstract_statement P;
        }

        return result;
    }

    public int after(Object result, boolean b) {
        if (b) {
            \abstract_statement Q1;
        }
        else {
            \abstract_statement Q2;
        }
        \abstract_statement P;

        return result;
    }
}