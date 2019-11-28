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
import java.awt.Dimension;
import java.awt.Font;

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
    private final JLabel secondaryStatusLabel;

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

        secondaryStatusLabel = new JLabel();
        secondaryStatusLabel.setHorizontalAlignment(SwingConstants.RIGHT);
        add(secondaryStatusLabel);

        statusLabel.setFont(new Font("Sans", Font.PLAIN, statusLabel.getFont().getSize()));
        secondaryStatusLabel.setFont(new Font("Sans", Font.PLAIN, statusLabel.getFont().getSize()));
    }

    public void setMessage(String message) {
        setMessage(message, true);
    }

    public void setMessage(String message, final boolean bold) {
        if (timeoutThread != null) {
            timeoutThread.interrupt();
        }

        if (changeThread != null) {
            changeThread.interrupt();
        }

        statusLabel.setIcon(null);
        if (bold) {
            statusLabel.setText(String.format("<html><b>%s</b></html>", message));
        } else {
            statusLabel.setText(String.format("<html>%s</html>", message));
        }

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

    public void setSecondaryMessage(String message) {
        secondaryStatusLabel.setText(String.format("<html>%s</html>", message));
    }

    private void changeThread() {
        this.changeThread = new Thread(() -> {
            while (!Thread.currentThread().isInterrupted()) {
                SwingUtilities.invokeLater(() -> {
                    statusLabel.setIcon(IconFontSwing.buildIcon( //
                            FontAwesomeSolid.LIGHTBULB, 16, Color.BLACK));
                    statusLabel
                            .setText(String.format("<html>%s</html>", standardMessages[currMsg]));
                });
                currMsg = (currMsg + 1) % standardMessages.length;

                try {
                    Thread.sleep(changeTime);
                } catch (InterruptedException e) {
                    return;
                }
            }
        });

        this.changeThread.start();
    }
}
