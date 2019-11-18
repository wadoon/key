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
package de.uka.ilkd.key.gui.abstractexecution.extension;

import java.awt.Color;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Collections;
import java.util.List;

import javax.swing.JButton;
import javax.swing.JToolBar;

import de.uka.ilkd.key.abstractexecution.relational.model.AERelationalModel;
import de.uka.ilkd.key.abstractexecution.relational.model.AbstractLocsetDeclaration;
import de.uka.ilkd.key.abstractexecution.relational.model.NullarySymbolDeclaration;
import de.uka.ilkd.key.abstractexecution.relational.model.PredicateDeclaration;
import de.uka.ilkd.key.abstractexecution.relational.model.ProgramVariableDeclaration;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.abstractexecution.relational.dialogs.AERelationalDialog;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;

/**
 * Extension adapter for showing hash codes for adding Abstract Execution-Based
 * GUI features for relational verification (e.g., of refactorings).
 *
 * @author Dominic Steinhoefel
 */
@KeYGuiExtension.Info( //
        name = "AE-Relational", //
        optional = true, //
        description = "Adds GUI features for relational proofs based on Abstract Execution.\n" //
                + "Developer: Dominic Steinhofel <steinhoefel@cs.tu-darmstadt.de>", //
        experimental = false)
public class AERelationalExtension implements KeYGuiExtension, KeYGuiExtension.Toolbar {

    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        final JToolBar result = new JToolBar("AE-Relational");

        final JButton openAERelationalWindowButton = new JButton("AE-Relational",
                IconFontSwing.buildIcon(FontAwesomeSolid.BALANCE_SCALE, 16, Color.BLACK));
        openAERelationalWindowButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                final String programOne = "";
                final String programTwo = "";
                final String postCondition = "\\result_1=\\result_2";
                final List<AbstractLocsetDeclaration> abstractLocationSets = Collections
                        .singletonList(new AbstractLocsetDeclaration("relevant"));
                final List<PredicateDeclaration> predicateDeclarations = Collections.emptyList();
                final List<ProgramVariableDeclaration> programVariableDeclarations = //
                        Collections.emptyList();
                final List<NullarySymbolDeclaration> relevantVarsOne = //
                        Collections.singletonList(abstractLocationSets.get(0));
                final List<NullarySymbolDeclaration> relevantVarsTwo = //
                        Collections.singletonList(abstractLocationSets.get(0));

                final AERelationalModel defaultModel = new AERelationalModel(programOne, programTwo,
                        postCondition, abstractLocationSets, predicateDeclarations,
                        programVariableDeclarations, relevantVarsOne, relevantVarsTwo);

                final AERelationalDialog dia = new AERelationalDialog(mainWindow, defaultModel);
                dia.setVisible(true);
            }
        });

        result.add(openAERelationalWindowButton);

        return result;
    }

}
