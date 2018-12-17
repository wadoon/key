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

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.AbstractExecutionTermLabel;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.TermTransformer;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * This {@link TermTransformer} adds an {@link AbstractExecutionTermLabel} to
 * the given term which refers to the {@link AbstractPlaceholderStatement} for
 * which it has been generated.
 *
 * @author Dominic Steinhoefel
 */
public final class AELabel extends AbstractTermTransformer {

    public AELabel() {
        super(new Name("#AELabel"), 3);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            Services services) {
        final Term abstrUpdTerm = term.sub(0);
        final AbstractPlaceholderStatement abstrProg =
                (AbstractPlaceholderStatement) term.sub(1).javaBlock().program()
                        .getFirstElement();
        final Term targetTerm = term.sub(2);

        final AbstractExecutionTermLabel label =
                new AbstractExecutionTermLabel(abstrProg);

        final TermBuilder tb = services.getTermBuilder();

        return tb.apply(tb.label(abstrUpdTerm, label), targetTerm);
    }
}