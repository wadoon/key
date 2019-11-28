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

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Window;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.List;
import java.util.stream.Collectors;

import javax.swing.AbstractAction;
import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JRootPane;
import javax.swing.JTextField;
import javax.swing.KeyStroke;

import de.uka.ilkd.key.abstractexecution.refinity.model.FuncOrPredDecl;
import de.uka.ilkd.key.abstractexecution.refinity.model.FunctionDeclaration;
import de.uka.ilkd.key.abstractexecution.refinity.model.PredicateDeclaration;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;

/**
 * @author Dominic Steinhoefel
 */
public class FuncAndPredInputDialog extends JDialog {
    private static final long serialVersionUID = 1L;

    private FuncOrPredDecl value;

    private FuncAndPredInputDialog(final Window owner, final FuncOrPredDecl value,
            Services services) {
        super(owner, ModalityType.DOCUMENT_MODAL);
        assert value != null;

        this.value = value;

        final FuncAndPredInputDialog instance = this;
        getContentPane().setLayout(new BorderLayout());

        final JPanel contentPanel = new JPanel();
        final int borderSize = 5;
        contentPanel.setBorder(
                BorderFactory.createEmptyBorder(borderSize, borderSize, borderSize, borderSize));
        contentPanel.setLayout(new BorderLayout());
        getContentPane().add(contentPanel, BorderLayout.CENTER);

        setTitle("Please enter a function or predicate symbol specification.");
        setResizable(false);

        final JButton okButton = new JButton("OK");

        final JTextField valueTextField = new JTextField(value.toString());
        valueTextField.addKeyListener(new KeyAdapter() {
            @Override
            public void keyTyped(KeyEvent e) {
                final char c = e.getKeyChar();

                if (!(c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9'
                        || c == '_' || c == ',' || c == '(' || c == ')' || c == '.' || c == ' ')) {
                    e.consume();
                }

                if (c == ' ' && !valueTextField.getText().matches("^[a-zA-Z0-9_]+$")) {
                    /*
                     * Cannot be the result sort of a function declaration. We admit at most one
                     * space.
                     */
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
                    final String input = valueTextField.getText();

                    final FuncOrPredDecl val;
                    if (input.contains(" ")) {
                        val = FunctionDeclaration.fromString(input);
                    } else {
                        val = PredicateDeclaration.fromString(input);
                    }

                    checkAndRegister(val, services);

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
        
        installEscapeListener();

        setSize(400, 110);
    }

    private void installEscapeListener() {
        final KeyStroke escape = KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0);
        final JRootPane rootPane = getRootPane();
        rootPane.getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW).put(escape, "cancel");
        rootPane.getActionMap().put("cancel", new AbstractAction() {
            private static final long serialVersionUID = 1L;

            @Override
            public void actionPerformed(ActionEvent e) {
                value = null;
                setVisible(false);
            }
        });
    }

    public static FuncOrPredDecl showInputDialog(final Window owner, Services services) {
        return showInputDialog(owner, PredicateDeclaration.EMPTY_DECL, services);
    }

    public static FuncOrPredDecl showInputDialog(final Window owner, final FuncOrPredDecl value,
            Services services) {
        final FuncAndPredInputDialog dia = new FuncAndPredInputDialog(owner, value, services);
        dia.setVisible(true);
        dia.dispose();
        return dia.value;
    }

    public static void checkAndRegister(final FuncOrPredDecl val, final Services services)
            throws ParserException {
        final NamespaceSet namespaces = services.getNamespaces();

        final List<Sort> sorts = val.getArgSorts().stream().map(namespaces.sorts()::lookup)
                .collect(Collectors.toList());

        for (int i = 0; i < sorts.size(); i++) {
            if (sorts.get(i) == null) {
                throw new ParserException("The sort " + val.getArgSorts().get(i) + " is unknown.",
                        null);
            }
        }

        if (val.isPredDecl()) {
            final PredicateDeclaration predDecl = val.toPredDecl();

            if (namespaces.functions().lookup(predDecl.getPredName()) != null) {
                throw new ParserException("The predicate " + predDecl.getPredName()
                        + " is already registered, please choose another one.", null);
            }

            namespaces.functions().add(new Function(new Name(predDecl.getPredName()), Sort.FORMULA,
                    sorts.toArray(new Sort[0])));
        } else {
            final FunctionDeclaration funcDecl = val.toFuncDecl();

            if (namespaces.functions().lookup(funcDecl.getFuncName()) != null) {
                throw new ParserException("The function " + funcDecl.getFuncName()
                        + " is already registered, please choose another one.", null);
            }

            final Sort targetSort = namespaces.sorts().lookup(funcDecl.getResultSortName());
            if (targetSort == null) {
                throw new ParserException(
                        "The sort " + funcDecl.getResultSortName() + " is unknown.", null);
            }

            namespaces.functions().add(new Function(new Name(funcDecl.getFuncName()), targetSort,
                    sorts.toArray(new Sort[0])));
        }
    }

}
