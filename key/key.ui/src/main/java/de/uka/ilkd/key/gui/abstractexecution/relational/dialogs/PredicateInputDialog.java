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
import java.util.List;
import java.util.stream.Collectors;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JTextField;

import de.uka.ilkd.key.abstractexecution.relational.model.PredicateDeclaration;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;

/**
 * @author Dominic Steinhoefel
 */
public class PredicateInputDialog extends JDialog {
    private static final long serialVersionUID = 1L;

    private PredicateDeclaration value;

    private PredicateInputDialog(final JDialog owner, final PredicateDeclaration value,
            Services services) {
        super(owner, true);
        assert value != null;

        this.value = value;

        final PredicateInputDialog instance = this;
        getContentPane().setLayout(new BorderLayout());

        final JPanel contentPanel = new JPanel();
        final int borderSize = 5;
        contentPanel.setBorder(
                BorderFactory.createEmptyBorder(borderSize, borderSize, borderSize, borderSize));
        contentPanel.setLayout(new BorderLayout());
        getContentPane().add(contentPanel, BorderLayout.CENTER);

        setTitle("Please enter a predicate specification.");
        setResizable(false);

        final JButton okButton = new JButton("OK");

        final JTextField valueTextField = new JTextField(value.toString());
        valueTextField.addKeyListener(new KeyAdapter() {
            @Override
            public void keyTyped(KeyEvent e) {
                final char c = e.getKeyChar();

                if (!(c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9'
                        || c == '_' || c == ',' || c == '(' || c == ')' || c == '.')) {
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
                    final PredicateDeclaration val = PredicateDeclaration
                            .fromString(valueTextField.getText());

                    final NamespaceSet namespaces = services.getNamespaces();
                    if (namespaces.functions().lookup(val.getPredName()) != null) {
                        throw new ParserException(
                                "The predicate " + val.getPredName()
                                        + " is already registered, please choose another one.",
                                null);
                    }

                    final List<Sort> sorts = val.getArgSorts().stream()
                            .map(namespaces.sorts()::lookup).collect(Collectors.toList());

                    for (int i = 0; i < sorts.size(); i++) {
                        if (sorts.get(i) == null) {
                            throw new ParserException(
                                    "The sort " + val.getArgSorts().get(i) + " is unknown.", null);
                        }
                    }

                    namespaces.functions().add(new Function(new Name(val.getPredName()),
                            Sort.FORMULA, sorts.toArray(new Sort[0])));

                    instance.value = val;
                    instance.setVisible(false);
                } catch (IllegalArgumentException exc) {
                    JOptionPane.showMessageDialog(instance,
                            "There's an error in your syntax, please correct it and try again",
                            "Syntax error", JOptionPane.ERROR_MESSAGE);
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

    public static PredicateDeclaration showInputDialog(final JDialog owner, Services services) {
        return showInputDialog(owner, PredicateDeclaration.EMPTY_DECL, services);
    }

    public static PredicateDeclaration showInputDialog(final JDialog owner,
            final PredicateDeclaration value, Services services) {
        final PredicateInputDialog dia = new PredicateInputDialog(owner, value, services);
        dia.setVisible(true);
        dia.dispose();
        return dia.value;
    }

}
