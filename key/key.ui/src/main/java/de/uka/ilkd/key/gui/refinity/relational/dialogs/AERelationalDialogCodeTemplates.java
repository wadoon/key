// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.gui.refinity.relational.dialogs;

/**
 * @author Dominic Steinhoefel
 */
public interface AERelationalDialogCodeTemplates {

    //@formatter:off
    static final String[][] CODE_TEMPLATES = new String[][] {
            new String[] { //
                    "aexp",
                    
                    "/*@ assignable frameE;\n" + //
                    "  @ accessible footprintE;\n" + //
                    "  @ exceptional_behavior requires false;\n" + //
                    "  @*/\n" + //
                    "\\abstract_expression boolean e"
            }, new String[] {
                    "as",
                    
                    "/*@ assignable frameP;\n" + //
                    "  @ accessible footprintP;\n" + //
                    "  @ exceptional_behavior requires false;\n" + //
                    "  @ return_behavior requires false;\n"+ //
                    "  @ break_behavior requires false;\n" + //
                    "  @ continue_behavior requires false;\n" + //
                    "  @*/\n" + //
                    "\\abstract_statement P;"
            }, new String[] {
                    "aec",
                    
                    "/*@ ae_constraint\n" + //
                    "  @   true;\n" + //
                    "  @*/\n" + //
                    "{ ; }"
            }
    };
    //@formatter:on
}
