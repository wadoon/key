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
import java.awt.Dimension;

import javax.swing.BorderFactory;
import javax.swing.BoxLayout;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.SwingConstants;
import javax.swing.SwingUtilities;
import javax.swing.border.BevelBorder;

import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;

/**
 * @author Dominic Steinhoefel
 */
public class AutoResetStatusPanel extends JPanel {
    private static final long serialVersionUID = 1L;

    private final String[] standardMessages;

    private final int timeout;
    private final int changeTime;

    private Thread timeoutThread = null;
    private Thread changeThread = null;

    private int currMsg = 0;

    private final JLabel statusLabel;

    public AutoResetStatusPanel(int timeout, int changeTime, String... standardMessages) {
        super();
        assert standardMessages != null && standardMessages.length > 0;

        this.standardMessages = standardMessages;
        this.timeout = timeout;
        this.changeTime = changeTime;

        setBorder(BorderFactory.createCompoundBorder(
                BorderFactory.createBevelBorder(BevelBorder.LOWERED),
                BorderFactory.createEmptyBorder(5, 5, 5, 5)));

        setPreferredSize(new Dimension(getPreferredSize().width, 32));
        setLayout(new BoxLayout(this, BoxLayout.X_AXIS));
        statusLabel = new JLabel(standardMessages[0]);
        statusLabel.setHorizontalAlignment(SwingConstants.LEFT);
        add(statusLabel);
    }

    public void setMessage(String message) {
        if (timeoutThread != null) {
            timeoutThread.interrupt();
        }

        if (changeThread != null) {
            changeThread.interrupt();
        }

        statusLabel.setIcon(null);
        statusLabel.setText(message);
        
        timeoutThread = new Thread(() -> {
            try {
                Thread.sleep(timeout);
            } catch (InterruptedException e) {
                return;
            }

            changeThread();
        });

        timeoutThread.start();
    }

    private void changeThread() {
        this.changeThread = new Thread(() -> {
            boolean interrupted = false;
            while (!interrupted) {
                SwingUtilities.invokeLater(() -> {
                    statusLabel.setIcon(IconFontSwing.buildIcon( //
                            FontAwesomeSolid.LIGHTBULB, 16, Color.BLACK));
                    statusLabel.setText(
                            String.format("<html>%s</html>", standardMessages[currMsg]));
                });
                currMsg = (currMsg + 1) % standardMessages.length;

                try {
                    Thread.sleep(changeTime);
                } catch (InterruptedException e) {
                    interrupted = true;
                }
            }
        });

        this.changeThread.start();
    }
}
