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
package de.uka.ilkd.key.gui.refinity.relational.components;

import java.awt.Color;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.function.Function;

import javax.swing.JTextArea;

import org.antlr.runtime.RecognitionException;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.parser.KeYLexerF;
import de.uka.ilkd.key.parser.KeYParserF;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;

/**
 * @author Dominic Steinhoefel
 */
public class FormulaInputTextArea extends JTextArea {
    private static final long serialVersionUID = 1L;

    private Services services = null;
    private Function<String, String> preprocessor = null;

    public FormulaInputTextArea(final String stdToolTip,
            final Function<String, String> preprocessor) {
        this.preprocessor = preprocessor;
        setToolTipText("<html>" + stdToolTip + "</html>");

        setBackground(Color.WHITE);

        addKeyListener(new KeyAdapter() {
            @Override
            public void keyReleased(KeyEvent e) {
                if (services != null) {
                    final FormulaInputTextArea textfield = FormulaInputTextArea.this;

                    String textToParse = textfield.getText();
                    if (FormulaInputTextArea.this.preprocessor != null) {
                        textToParse = FormulaInputTextArea.this.preprocessor.apply(textToParse);
                    }

                    final KeYLexerF lexer = new KeYLexerF( //
                            "\\problem { " + textToParse + "}", "No file.");

                    final KeYParserF parser = new KeYParserF(ParserMode.TACLET, lexer,
                            GoalLocalSpecificationRepository.DUMMY_REPO, services,
                            services.getNamespaces());

                    try {
                        parser.parseProblem();
                        textfield.setBackground(Color.WHITE);
                        setToolTipText("<html>" + stdToolTip + "</html>");
                    } catch (RecognitionException exc) {
                        textfield.setBackground(Color.RED);
                        if (exc.getMessage() != null && !exc.getMessage().isEmpty()) {
                            setToolTipText("<html>" + exc.getMessage().replaceAll("\\n", "<br/>")
                                    + "<br/><br/>" + stdToolTip + "</html>");
                        } else {
                            setToolTipText(exc.toString());
                        }
                    }
                }
            }
        });
    }

    public void setPreprocessor(Function<String, String> preprocessor) {
        this.preprocessor = preprocessor;
    }

    public void setServices(Services services) {
        this.services = services;
    }

}
