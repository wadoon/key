// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.visitor;

import java.util.function.Function;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;

/**
 * TODO
 *
 * @author Dominic Scheurer
 */
public class ProgramElementPrepender extends CreatingASTVisitor {

    Function<ProgramElement, Boolean> filter;
    private ProgramElement newElement;

    public ProgramElementPrepender(JavaProgramElement program,
            Services services) {
        super(program, false, services);
    }

    public ProgramElement append(Function<ProgramElement, Boolean> filter,
            ProgramElement toAppend) {
        this.filter = filter;
        this.newElement = toAppend;

        stack.push(new ExtList());
        walk(root());
        ExtList el = stack.peek();
        return el.get(ProgramElement.class);
    }

    protected void doAction(ProgramElement element) {
        if (filter.apply(element)) {
            addChild(new StatementBlock((Statement) newElement,
                    (Statement) element));
            changed();
        } else {
            super.doAction(element);
        }
    }

}