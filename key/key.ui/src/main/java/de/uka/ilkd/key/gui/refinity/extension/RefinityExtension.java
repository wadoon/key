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
package de.uka.ilkd.key.gui.refinity.extension;

import java.awt.Color;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.net.URL;

import javax.swing.BorderFactory;
import javax.swing.Icon;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JToolBar;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.gui.refinity.dialogs.RefinityWindow;

/**
 * Extension adapter for showing hash codes for adding Abstract Execution-Based
 * GUI features for relational verification (e.g., of refactorings).
 *
 * @author Dominic Steinhoefel
 */
@KeYGuiExtension.Info( //
        name = "AE-Relational", //
        optional = true, //
        description = "Adds the REFINITY button for starting the GUI of the relational verification extension REFINITY.\n" //
                + "Developer: Dominic Steinhofel <steinhoefel@cs.tu-darmstadt.de>", //
        experimental = false)
public class RefinityExtension implements KeYGuiExtension, KeYGuiExtension.Toolbar {
    private static final String REFINITY_LOGO = "/de/uka/ilkd/key/gui/refinity/refinity-logo-w-bg.png";

    private static final String TOOLTIP = "Opens dialog of the Abstract Execution-based relational verification tool REFINITY.";
    private static final Color BG_COLOR = Color.decode("#23373b");
    private static final Color FG_COLOR = Color.decode("#FAFAFA");
    private static final Color HL_COLOR = Color.decode("#EB811B");

    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        final JToolBar result = new JToolBar("AE-Relational");

        final JButton openAERelationalWindowButton = new JButton("REFINITY",
                IconFontSwing.buildIcon(FontAwesomeSolid.BALANCE_SCALE, 16, Color.BLACK));
        openAERelationalWindowButton.setToolTipText(
                "<html><table><tr><td width=\"140px\">" + TOOLTIP + "</td></tr></table></html>");

        final URL refinityLogoURL = RefinityExtension.class.getResource(REFINITY_LOGO);
        if (refinityLogoURL != null) {
            final Icon refinityLogo = new ImageIcon(refinityLogoURL);
            openAERelationalWindowButton.setText("");
            openAERelationalWindowButton.setIcon(refinityLogo);
            openAERelationalWindowButton.setBorder(BorderFactory.createLineBorder(BG_COLOR, 1));

            openAERelationalWindowButton.addMouseListener(new MouseAdapter() {
                @Override
                public void mouseEntered(MouseEvent e) {
                    openAERelationalWindowButton
                            .setBorder(BorderFactory.createLineBorder(FG_COLOR, 1));
                }

                @Override
                public void mouseExited(MouseEvent e) {
                    openAERelationalWindowButton
                            .setBorder(BorderFactory.createLineBorder(BG_COLOR, 1));
                }

                @Override
                public void mousePressed(MouseEvent e) {
                    openAERelationalWindowButton
                            .setBorder(BorderFactory.createLineBorder(HL_COLOR, 1));
                }
            });
        }

        openAERelationalWindowButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                openNewDefaultRefinityWindow(mainWindow);
            }
        });

        result.add(openAERelationalWindowButton);

        return result;
    }

    public static void openNewDefaultRefinityWindow(MainWindow mainWindow) {
        new RefinityWindow(mainWindow).setVisible(true);
    }

}