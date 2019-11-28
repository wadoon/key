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

import java.awt.Dimension;

import javax.swing.Action;
import javax.swing.Icon;
import javax.swing.JButton;

/**
 * @author Dominic Steinhoefel
 */
public class JSizedButton extends JButton {
    private static final long serialVersionUID = 1L;
    
    private final int width;
    private final int height;

    public JSizedButton(int width, int height) {
        this.width = width;
        this.height = height;
    }

    public JSizedButton(Action a, int width, int height) {
        super(a);
        this.width = width;
        this.height = height;
    }

    public JSizedButton(Icon icon, int width, int height) {
        super(icon);
        this.width = width;
        this.height = height;
    }

    public JSizedButton(String text, Icon icon, int width, int height) {
        super(text, icon);
        this.width = width;
        this.height = height;
    }

    public JSizedButton(String text, int width, int height) {
        super(text);
        this.width = width;
        this.height = height;
    }
    
    @Override
    public Dimension getMinimumSize() {
        return dimension();
    }
    
    @Override
    public Dimension getPreferredSize() {
        return dimension();
    }
    
    @Override
    public Dimension getMaximumSize() {
        return dimension();
    }

    private Dimension dimension() {
        return new Dimension(width, height);
    }

}
