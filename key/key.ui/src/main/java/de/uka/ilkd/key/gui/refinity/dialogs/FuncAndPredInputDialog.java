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

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.Window;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.util.Optional;

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

/**
 * @author Dominic Steinhoefel
 */
public class FuncAndPredInputDialog extends JDialog {
    private static final long serialVersionUID = 1L;

    private FuncOrPredDecl value;

    protected FuncAndPredInputDialog(final Window owner, final FuncOrPredDecl value,
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

        setTitle(windowTitle());
        setResizable(false);

        final JButton okButton = new JButton("OK");

        final JTextField valueTextField = new JTextField(renderValue(value));
        valueTextField.setToolTipText(inputTooltipText());
        valueTextField
                .setFont(new Font("Monospaced", Font.PLAIN, valueTextField.getFont().getSize()));
        valueTextField.addActionListener(e -> okButton.doClick());

        contentPanel.add(valueTextField, BorderLayout.CENTER);

        final JPanel buttonPanel = new JPanel(new FlowLayout(FlowLayout.CENTER));

        okButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                try {
                    final FuncOrPredDecl val = parseString(valueTextField.getText());

                    val.checkAndRegister(services);

                    instance.value = val;
                    instance.setVisible(false);
                } catch (IllegalArgumentException exc) {
                    JOptionPane.showMessageDialog(instance,
                            "There's an error in your syntax, please correct it and try again",
                            "Syntax error", JOptionPane.ERROR_MESSAGE);
                } catch (RuntimeException exc) {
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

    protected FuncOrPredDecl getValue() {
        return value;
    }

    protected String renderValue(final FuncOrPredDecl value) {
        return value.toString();
    }

    protected FuncOrPredDecl parseString(final String input) throws IllegalArgumentException {
        Optional<? extends FuncOrPredDecl> maybeVal = FunctionDeclaration.fromString(input);

        if (!maybeVal.isPresent()) {
            maybeVal = PredicateDeclaration.fromString(input);
        }

        if (!maybeVal.isPresent()) {
            throw new IllegalArgumentException();
        }

        return maybeVal.get();
    }

    protected String inputTooltipText() {
        return "<html>Example: \"<tt>ThrowsExcP(any)</tt>\", \"<tt>Post(any,int)</tt>\","
                + " \"<tt>int myFun(java.lang.Object)</tt>\"</html>";
    }

    protected String windowTitle() {
        return "Please enter a function or predicate symbol specification.";
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

}