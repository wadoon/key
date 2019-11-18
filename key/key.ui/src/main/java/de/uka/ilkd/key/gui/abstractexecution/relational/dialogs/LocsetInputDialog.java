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
import java.awt.Window;
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

import de.uka.ilkd.key.abstractexecution.relational.model.AbstractLocsetDeclaration;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.parser.ParserException;

/**
 * @author Dominic Steinhoefel
 */
public class LocsetInputDialog extends JDialog {
    private static final long serialVersionUID = 1L;

    private AbstractLocsetDeclaration value;

    private LocsetInputDialog(final Window owner, final AbstractLocsetDeclaration value,
            Services services) {
        super(owner, ModalityType.DOCUMENT_MODAL);
        assert value != null;

        this.value = value;

        final LocsetInputDialog instance = this;
        getContentPane().setLayout(new BorderLayout());

        final JPanel contentPanel = new JPanel();
        final int borderSize = 5;
        contentPanel.setBorder(
                BorderFactory.createEmptyBorder(borderSize, borderSize, borderSize, borderSize));
        contentPanel.setLayout(new BorderLayout());
        getContentPane().add(contentPanel, BorderLayout.CENTER);

        setTitle("Please enter a name for the LocSet constant.");
        setResizable(false);

        final JButton okButton = new JButton("OK");

        final JTextField valueTextField = new JTextField(value.getLocsetName());
        valueTextField.addKeyListener(new KeyAdapter() {
            @Override
            public void keyTyped(KeyEvent e) {
                final char c = e.getKeyChar();

                if (!(c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9'
                        || c == '_')) {
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
                final AbstractLocsetDeclaration val = //
                        new AbstractLocsetDeclaration(valueTextField.getText());

                try {
                    checkAndRegister(val, services);

                    instance.value = val;
                    instance.setVisible(false);
                } catch (ParserException exc) {
                    JOptionPane.showMessageDialog(instance,
                            "<html>There's an error in your syntax, please correct it and try again"
                                    + "<br/><br/>Message:<br/>" + exc.getMessage() + "<html>",
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

    public static AbstractLocsetDeclaration showInputDialog(final Window owner,
            Services services) {
        return showInputDialog(owner, AbstractLocsetDeclaration.EMPTY_DECL, services);
    }

    public static AbstractLocsetDeclaration showInputDialog(final Window owner,
            final AbstractLocsetDeclaration value, Services services) {
        final LocsetInputDialog dia = new LocsetInputDialog(owner, value, services);
        dia.setVisible(true);
        dia.dispose();
        return dia.value;
    }

    public static void checkAndRegister(final AbstractLocsetDeclaration val,
            final Services services) throws ParserException {
        final NamespaceSet namespaces = services.getNamespaces();
        if (namespaces.functions().lookup(val.getLocsetName()) != null) {
            throw new ParserException(
                    "The name " + val + " is already registered, please choose another one.", null);
        }

        namespaces.functions().add(new Function(new Name(val.getLocsetName()),
                services.getTypeConverter().getLocSetLDT().targetSort()));
    }

}
