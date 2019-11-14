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
package de.uka.ilkd.key.gui.abstractexecution.relational.components;

import java.awt.Color;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;

import javax.swing.BorderFactory;
import javax.swing.JTextField;

import org.antlr.runtime.RecognitionException;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.parser.KeYLexerF;
import de.uka.ilkd.key.parser.KeYParserF;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;

/**
 * @author Dominic Steinhoefel
 */
public class FormulaInputTextField extends JTextField {
    private static final long serialVersionUID = 1L;

    private Services services = null;

    public FormulaInputTextField() {
        setBackground(Color.WHITE);
        setBorder(BorderFactory.createCompoundBorder(getBorder(),
                BorderFactory.createEmptyBorder(5, 5, 5, 5)));

        addKeyListener(new KeyAdapter() {
            @Override
            public void keyReleased(KeyEvent e) {
                if (services != null) {
                    final FormulaInputTextField textfield = FormulaInputTextField.this;

                    final KeYLexerF lexer = new KeYLexerF(
                            "\\problem { " + textfield.getText() + "}", "No file.");

                    final KeYParserF parser = new KeYParserF(ParserMode.TACLET, lexer,
                            GoalLocalSpecificationRepository.DUMMY_REPO, services,
                            services.getNamespaces());

                    try {
                        parser.parseProblem();
                        textfield.setBackground(Color.WHITE);
                        setToolTipText(null);
                    } catch (RecognitionException exc) {
                        textfield.setBackground(Color.RED);
                        if (exc.getMessage() != null && !exc.getMessage().isEmpty()) {
                            setToolTipText("<html>" + exc.getMessage().replaceAll("\\n", "<br/>")
                                    + "</html>");
                        } else {
                            setToolTipText(exc.toString());
                        }
                    }
                }
            }
        });
    }

    public void setServices(Services services) {
        this.services = services;
    }

}
