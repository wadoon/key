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
package de.uka.ilkd.key.gui.abstractexecution.relational.dialogs;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JTextField;

import de.uka.ilkd.key.abstractexecution.relational.model.ProgramVariableDeclaration;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * @author Dominic Steinhoefel
 */
public class ProgramVariableInputDialog extends JDialog {
    private static final long serialVersionUID = 1L;

    private ProgramVariableDeclaration value;

    private ProgramVariableInputDialog(final JDialog owner, final ProgramVariableDeclaration value,
            Services services) {
        super(owner, true);
        assert value != null;

        this.value = value;

        final ProgramVariableInputDialog instance = this;
        getContentPane().setLayout(new BorderLayout());

        final JPanel contentPanel = new JPanel();
        final int borderSize = 5;
        contentPanel.setBorder(
                BorderFactory.createEmptyBorder(borderSize, borderSize, borderSize, borderSize));
        contentPanel.setLayout(new BorderLayout());
        getContentPane().add(contentPanel, BorderLayout.CENTER);

        setTitle("Please enter a program variable specification.");
        setResizable(false);

        final JButton okButton = new JButton("OK");

        final JTextField valueTextField = new JTextField(value.toString());
        valueTextField.addKeyListener(new KeyAdapter() {
            @Override
            public void keyTyped(KeyEvent e) {
                final char c = e.getKeyChar();

                if (!(c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9'
                        || c == '_' || c == ',' || c == ' ' || c == '.')) {
                    e.consume();
                }
            }
        });
        valueTextField.addActionListener(e -> okButton.doClick());

        contentPanel.add(valueTextField, BorderLayout.CENTER);

        final JPanel buttonPanel = new JPanel(new FlowLayout(FlowLayout.CENTER));

        okButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                try {
                    final ProgramVariableDeclaration val = ProgramVariableDeclaration
                            .fromString(valueTextField.getText());

                    checkAndRegister(val, services);

                    instance.value = val;
                    instance.setVisible(false);
                } catch (IllegalArgumentException exc) {
                    JOptionPane.showMessageDialog(instance,
                            "There's an error in your syntax, please correct it and try again",
                            "Syntax error", JOptionPane.ERROR_MESSAGE);
                } catch (RuntimeException exc) {
                    JOptionPane.showMessageDialog(instance,
                            "<html>There's an error in your syntax, please correct it and try again<br/><br/>Message:<br/>"
                                    + exc.getMessage() + "</html>",
                            "Syntax error", JOptionPane.ERROR_MESSAGE);
                }
            }
        });
        final JButton cancelButton = new JButton("Cancel");
        cancelButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                instance.value = null;
                instance.setVisible(false);
            }
        });

        okButton.setPreferredSize(new Dimension(90, okButton.getPreferredSize().height));
        cancelButton.setPreferredSize(new Dimension(90, cancelButton.getPreferredSize().height));

        buttonPanel.add(okButton);
        buttonPanel.add(cancelButton);
        contentPanel.add(buttonPanel, BorderLayout.SOUTH);

        setSize(400, 110);
    }

    public static void checkAndRegister(final ProgramVariableDeclaration val,
            final Services services) {
        final Sort sort = services.getNamespaces().sorts().lookup(val.getTypeName());

        if (sort == null) {
            throw new RuntimeException("Sort \"" + val.getTypeName() + "\" is not known");
        }

        final Name name = new Name(val.getVarName());

        if (services.getNamespaces().lookup(name) != null) {
            throw new RuntimeException("The name \"" + val.getVarName()
                    + "\" is already known to the system.<br/>\n" + "Plase choose a fresh one.");
        }

        services.getNamespaces().programVariables()
                .add(new LocationVariable(new ProgramElementName(val.getVarName()),
                        services.getJavaInfo().getKeYJavaType(sort)));
    }

    public static ProgramVariableDeclaration showInputDialog(final JDialog owner,
            Services services) {
        return showInputDialog(owner, ProgramVariableDeclaration.EMPTY_DECL, services);
    }

    public static ProgramVariableDeclaration showInputDialog(final JDialog owner,
            final ProgramVariableDeclaration value, Services services) {
        final ProgramVariableInputDialog dia = new ProgramVariableInputDialog(owner, value,
                services);
        dia.setVisible(true);
        dia.dispose();
        return dia.value;
    }

}
