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
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;

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

import de.uka.ilkd.key.abstractexecution.refinity.model.ProgramVariableDeclaration;
import de.uka.ilkd.key.java.Services;

/**
 * @author Dominic Steinhoefel
 */
public class ProgramVariableInputDialog extends JDialog {
    private static final long serialVersionUID = 1L;

    private ProgramVariableDeclaration value;

    private ProgramVariableInputDialog(final Window owner, final ProgramVariableDeclaration value,
            Services services) {
        super(owner, ModalityType.DOCUMENT_MODAL);
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
        valueTextField.setToolTipText(
                "<html>Example: \"<tt>int i</tt>\", \"<tt>java.lang.Object obj</tt>\"</html>");
        valueTextField
                .setFont(new Font("Monospaced", Font.PLAIN, valueTextField.getFont().getSize()));
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

                    val.checkAndRegister(services);

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

    public static ProgramVariableDeclaration showInputDialog(final Window owner,
            Services services) {
        return showInputDialog(owner, ProgramVariableDeclaration.EMPTY_DECL, services);
    }

    public static ProgramVariableDeclaration showInputDialog(final Window owner,
            final ProgramVariableDeclaration value, Services services) {
        final ProgramVariableInputDialog dia = new ProgramVariableInputDialog(owner, value,
                services);
        dia.setVisible(true);
        dia.dispose();
        return dia.value;
    }

}