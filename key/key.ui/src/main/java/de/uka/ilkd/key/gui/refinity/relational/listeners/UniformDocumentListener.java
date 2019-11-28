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

import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;

public abstract class UniformDocumentListener implements DocumentListener {
    @Override
    public void changedUpdate(DocumentEvent e) {
        documentChanged(e);
    }

    @Override
    public void insertUpdate(DocumentEvent e) {
        documentChanged(e);
    }

    @Override
    public void removeUpdate(DocumentEvent e) {
        documentChanged(e);
    }

    public abstract void documentChanged(DocumentEvent e);
    
    public static UniformDocumentListener udl(Consumer<DocumentEvent> f) {
        return new UniformDocumentListener() {
            @Override
            public void documentChanged(DocumentEvent e) {
                f.accept(e);
            }
        };
    }
}