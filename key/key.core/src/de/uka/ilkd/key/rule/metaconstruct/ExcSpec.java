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

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;

/**
 * Term transformer which relates, in the context of Abstract Execution, the
 * exception flag of an {@link AbstractPlaceholderStatement} with a potentially
 * existing exceptional_behavior precondition. More precisely, it creates the
 * formula "!(exc = null) <-> PRECONDITION".
 *
 * @author Dominic Steinhöfel
 */
public class ExcSpec extends AbstractTermTransformer {

    public ExcSpec() {
        super(new Name("#excSpec"), 2);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final AbstractPlaceholderStatement abstrStmt = (AbstractPlaceholderStatement) svInst
                .getInstantiation((SchemaVariable) term.sub(0).op());

        final LocationVariable excFlag = (LocationVariable) term.sub(1).op();

        final ImmutableSet<BlockContract> contracts = services
                .getSpecificationRepository()
                .getAbstractPlaceholderStatementContracts(abstrStmt);

        for (final BlockContract contract : contracts) {
            if (contract.getBaseName()
                    .contains(Behavior.EXCEPTIONAL_BEHAVIOR.toString())) {
                return tb.equals(tb.not(tb.equals(tb.var(excFlag), tb.NULL())),
                        contract.getPre(services));
            }
        }

        return tb.tt();
    }
}