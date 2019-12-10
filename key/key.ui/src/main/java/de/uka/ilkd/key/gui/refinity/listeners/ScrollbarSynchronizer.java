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
package de.uka.ilkd.key.gui.refinity.listeners;

import java.awt.event.AdjustmentEvent;
import java.awt.event.AdjustmentListener;
import java.util.Arrays;

import javax.swing.JScrollBar;

/**
 * Synchronizes two scroll bars.
 * 
 * @see https://stackoverflow.com/questions/35718046/2-synchronized-jscrollpanes-inside-jsplitpane-not-working-properly
 * @author camickr (StackOverflow)
 * @author Dominic Steinhoefel
 */
public class ScrollbarSynchronizer implements AdjustmentListener {
    private final JScrollBar[] scrollBars;

    public static void synchronize(final JScrollBar... scrollBars) {
        final ScrollbarSynchronizer synchronizer = new ScrollbarSynchronizer(scrollBars);

        for (final JScrollBar scrollBar : scrollBars) {
            scrollBar.addAdjustmentListener(synchronizer);
        }
    }

    public static void unSynchronize(final JScrollBar... scrollBars) {
        Arrays.stream(scrollBars)
                .forEach(sb -> Arrays.stream(sb.getAdjustmentListeners())
                        .filter(ScrollbarSynchronizer.class::isInstance)
                        .forEach(l -> sb.removeAdjustmentListener(l)));
    }

    private ScrollbarSynchronizer(final JScrollBar... scrollBars) {
        this.scrollBars = scrollBars;
    }

    @Override
    public void adjustmentValueChanged(AdjustmentEvent e) {
        final JScrollBar source = (JScrollBar) e.getSource();
        int value = e.getValue();

        for (final JScrollBar scrollBar : scrollBars) {
            if (scrollBar != source) {
                scrollBar.removeAdjustmentListener(this);
                scrollBar.setValue(value);
                scrollBar.addAdjustmentListener(this);
            }
        }
    }
}
