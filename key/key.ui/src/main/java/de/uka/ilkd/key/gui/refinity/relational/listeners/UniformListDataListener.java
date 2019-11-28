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
package de.uka.ilkd.key.gui.refinity.relational.listeners;

import java.util.function.Consumer;

import javax.swing.event.ListDataEvent;
import javax.swing.event.ListDataListener;

public abstract class UniformListDataListener implements ListDataListener {
    @Override
    public void contentsChanged(ListDataEvent e) {
        listChanged(e);
    }

    @Override
    public void intervalAdded(ListDataEvent e) {
        listChanged(e);
    }

    @Override
    public void intervalRemoved(ListDataEvent e) {
        listChanged(e);
    }

    public abstract void listChanged(ListDataEvent e);

    public static UniformListDataListener uldl(Consumer<ListDataEvent> f) {
        return new UniformListDataListener() {
            @Override
            public void listChanged(ListDataEvent e) {
                f.accept(e);
            }
        };
    }
}