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
package de.uka.ilkd.key.gui.refinity.dialogs;

import java.awt.Color;
import java.util.Arrays;
import java.util.stream.Collectors;

/**
 * @author Dominic Steinhoefel
 */
public interface RefinityWindowConstants extends RefinityWindowCodeTemplates {
    static final String DUMMY_KEY_FILE = "/de/uka/ilkd/key/gui/refinity/dummy.key";
    static final String PROOF_BUNDLE_ENDING = ".zproof";

    //////////////////////
    // TITLE COMPONENTS //
    //////////////////////

    /*
     * Placeholder %s is for version number, which comes with leading space if
     * successfully read
     */
    static final String TITLE = "REFINITY%s \u2014 Relational Proofs with Abstract Execution";
    static final String DIRTY_TITLE_PART = " *";
    static final String READ_ONLY_TITLE_PART = " (READ ONLY - Save to edit)";

    //////////////////
    // STATUS PANEL //
    //////////////////

    static final int STATUS_PANEL_TIMEOUT = 2000;
    static final int STATUS_PANEL_CHANGE_TIME = 30000;
    static final String STATUS_PANEL_STD_MSG_1 = //
            "Try to use tooltips if feeling unsure about the functionality of an element.";
    static final String STATUS_PANEL_STD_MSG_2 = //
            "Recommended Example: File > Load Example > Abstract Execution > Consolidate Duplicate... > Extract Prefix";
    static final String STATUS_PANEL_STD_MSG_3 = createCodeTemplateMessage();

    static String createCodeTemplateMessage() {
        return "There are code templates for abstract statements, expressions, and constraints! Type "
                + Arrays.stream(CODE_TEMPLATES).map(arr -> arr[0])
                        .map(templateID -> String.format("\"<tt>%s</tt>\"", templateID))
                        .collect(Collectors.joining(" / "))
                + " followed by <tt>Ctrl+Shift+Space</tt> (Mac: <tt>Command+Shift+Space</tt>).";
    }

    ////////////////////
    // FONTS & COLORS //
    ////////////////////

    static final Color COMMENT_COLOR = Color.decode("#373D3F");

    //////////////
    // TOOLTIPS //
    //////////////

    static final String CLOSE_BUTTON_TOOLTIP = htmlTooltip(
            "Closes the REFINITY and KeY windows and terminates the application.", 100);
    static final String CHECK_SYNTAX_TOOLTIP = htmlTooltip(
            "Performs a syntax check of JML + Java code with KeY (more expensive than the continuous Java-only check)", 150);
    static final String STD_PRECONDREL_TOOLTIP = "Relational precondition (JML formula).";
    static final String STD_POSTCONDREL_TOOLTIP = "Relation between values of the relevant locations after execution (JML formula).<br/>"
            + "You may use the keywords \"\\result_1\" and \"\\result_2\" to access<br/>"
            + "the respective result arrays.<br/>"
            + "Access individual values with \"\\result_1[2]\" etc. Use type casts<br/>"
            + "in non-trivial compound expressions.<br/>"
            + "At position [0], a returned value will be accessible.<br/>"
            + "At position [1], a potentially thrown Exception object will be<br/>"
            + "accessible which is null if no exception was thrown.<br/>";
    static final String LOCSET_DECL_TOOLTIP = "<html>Abstract location sets for use in dynamic frames and footprints.<br/>"
            + "Syntax: E.g., 'nameForLocSet'.<br/>"
            + "Those locations can be used as 'relevant locations'.</html>";
    static final String PROGVAR_DECL_TOOLTIP = "<html>Program variables available without declaration.<br/>"
            + "Syntax: E.g., 'int x', or 'java.lang.Object y'.<br/>"
            + "Those variables can be used as 'relevant locations'.</html>";
    static final String FUNC_OR_PRED_DECL_TOOLTIP = "<html>Funcion or predicate symbols that can, e.g., be used to control<br/>"
            + "abrupt completion of abstract program elements.<br/>"
            + "Syntax: E.g., 'throwsExcP(any)' or 'int myFun(java.lang.Object).<br/>"
            + "Can be used, e.g., in 'assumes' clauses in the abstract<br/>"
            + " program models.</html>";
    static final String SAVE_BTN_TOOLTIP = "<html>Creates a KeY proof bundle at a temporary<br/>"
            + "location and starts the proof.</html>";
    static final String CHECK_PROOF_BTN_TOOLTIP = "<html>Loads a proof file and attempts to certify<br/>"
            + "that it is a proof of this model.</html>";
    static final String TOOLTIP_REL_LOCS_RIGHT = htmlTooltip(
            "Locations that are part of the result relation (for the right program).<br/>"
                    + "The i-th location in this list (i >= 1) is available via "
                    + "\\result_2[i+1] in the 'Relation to Verify' text field.",
            180);
    static final String TOOLTIP_REL_LOCS_LEFT = htmlTooltip(
            "Locations that are part of the result relation (for the left program).<br/>"
                    + "The i-th location in this list (i >= 1) is available via "
                    + "\\result_1[i+1] in the 'Relation to Verify' text field.",
            180);
    static final String CONTEXT_TOOLTIP = htmlTooltip(
            "The surrounding context. Method-level, i.e., everything "
                    + "you could write <em>inside</em> a class, especially field and method "
                    + "declarations. The specified context is used for <em>both</em> abstract "
                    + "program fragments.",
            160);
    static final String APF_TOOLTIP = htmlTooltip(
            "The abstract program fragments for which to prove "
                    + "the desired relation. Statement-level, i.e, everything you "
                    + "could write inside a method body. You can use the declared "
                    + "program variables and, inside JML specifications, the declared "
                    + "abstract location sets and predicates.",
            180);

    static String htmlTooltip(String text, int width) {
        return String.format(
                "<html><table><td width=\"%dpx\" style=\"text-align:justify;\">%s</td></tr></html>",
                width, text);
    }

}
