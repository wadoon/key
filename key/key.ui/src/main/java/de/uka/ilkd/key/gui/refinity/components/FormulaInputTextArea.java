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
package de.uka.ilkd.key.gui.refinity.components;

import java.awt.Color;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.function.Function;

import javax.swing.JTextArea;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.translation.JMLTranslator;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;

/**
 * @author Dominic Steinhoefel
 */
public class FormulaInputTextArea extends JTextArea {
    private static final long serialVersionUID = 1L;

    private Services services = null;
    private KeYJavaType kjt = null;
    private Function<String, String> preprocessor = null;

    public FormulaInputTextArea(final String stdToolTip,
            final Function<String, String> preprocessor) {
        this.preprocessor = preprocessor;
        setToolTipText("<html>" + stdToolTip + "</html>");

        setBackground(Color.WHITE);

        addKeyListener(new KeyAdapter() {
            @Override
            public void keyReleased(KeyEvent e) {
                if (services != null && kjt != null) {
                    final FormulaInputTextArea textfield = FormulaInputTextArea.this;

                    String textToParse = textfield.getText();
                    if (FormulaInputTextArea.this.preprocessor != null) {
                        textToParse = FormulaInputTextArea.this.preprocessor.apply(textToParse);
                    }

                    try {
                        JMLTranslator.translate(new PositionedString(textToParse), kjt, null, null,
                                null, null, null, null, Term.class, services);
                        textfield.setForeground(Color.BLACK);
                        setToolTipText("<html>" + stdToolTip + "</html>");
                    } catch (SLTranslationException | RuntimeException exc) {
                        textfield.setForeground(Color.RED);
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

    public void setKeYJavaTypeForJMLParsing(KeYJavaType kjt) {
        this.kjt = kjt;
    }

}
