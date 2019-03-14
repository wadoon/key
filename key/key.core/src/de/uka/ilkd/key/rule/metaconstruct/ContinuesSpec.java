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

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.java.Services;
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
 * continues flag of an {@link AbstractPlaceholderStatement} with a potentially
 * existing continues behavior precondition. More precisely, it creates the
 * formula "continues <-> PRECONDITION".
 *
 * @author Dominic Steinhoefel
 */
public class ContinuesSpec extends AbstractTermTransformer {

    public ContinuesSpec() {
        super(new Name("#continuesSpec"), 2);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final AbstractPlaceholderStatement abstrStmt = (AbstractPlaceholderStatement) svInst
                .getInstantiation((SchemaVariable) term.sub(0).op());

        final LocationVariable continuesFlag = (LocationVariable) term.sub(1)
                .op();

        final ImmutableSet<BlockContract> contracts = services
                .getSpecificationRepository()
                .getAbstractPlaceholderStatementContracts(abstrStmt);

        for (final BlockContract contract : contracts) {
            if (contract.getBaseName()
                    .contains(Behavior.CONTINUE_BEHAVIOR.toString())) {
                return tb.equals(tb.equals(tb.var(continuesFlag), tb.TRUE()),
                        contract.getPre(services));
            }
        }

        return tb.tt();
    }
}