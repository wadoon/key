// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.macros;

/**
 * This class captures a proof macro which is meant to fully automise KeY proof
 * workflow.
 *
 * It is experimental.
 *
 * It performs the following steps:
 * <ol>
 * <li>Finish symbolic execution
 * <li>>Separate proof obligations" +
 * <li>Expand invariant definitions
 * <li>Try to close all proof obligations
 * </ol>
 *
 * @author mattias ulbrich
 */
public class ScriptAwareMacro extends SequentialProofMacro {

    @Override
    public String getName() {
        return "Script-aware Auto";
    }

    @Override
    public String getCategory() {
        return "Auto Pilot";
    }

    @Override
    public String getScriptCommandName() {
        return "script-auto";
    }


    @Override
    public String getDescription() {
        return "<html>todo";
    }

    @Override
    protected ProofMacro[] createProofMacroArray() {
        ScriptAwareAutoMacro autoMacro = new ScriptAwareAutoMacro();
        return new ProofMacro[] {
                autoMacro,
                new ApplyScriptsMacro(autoMacro.getDetectedCommands())
        };
    }
}
