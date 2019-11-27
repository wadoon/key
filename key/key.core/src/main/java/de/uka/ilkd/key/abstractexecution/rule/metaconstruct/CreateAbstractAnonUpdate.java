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

package de.uka.ilkd.key.abstractexecution.rule.metaconstruct;

import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import org.key_project.util.collection.UniqueArrayList;

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractStatement;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.HasToLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.SkolemLoc;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Creates the anonymizing update for abstract location sets. Expects as
 * arguments the loop formula (for getting the loop specification, i.e., the
 * modifies clause).
 *
 * @author Dominic Steinhoefel
 */
public final class CreateAbstractAnonUpdate extends AbstractTermTransformer {

    public CreateAbstractAnonUpdate() {
        super(new Name("#createAbstractAnonUpdate"), 1);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            GoalLocalSpecificationRepository localSpecRepo, Services services) {
        final ExecutionContext ec = svInst.getExecutionContext();
        final Term loopTerm = term.sub(0);
        final Optional<LoopSpecification> loopSpec = //
                MiscTools.getSpecForTermWithLoopStmt(loopTerm, localSpecRepo);

        if (!loopSpec.isPresent()) {
            return null;
        }

        return createHeapAnonUpdate(loopSpec.get(), ec, services);
    }

    private static Term createHeapAnonUpdate(LoopSpecification loopSpec, final ExecutionContext ec,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Map<LocationVariable, Term> atPres = loopSpec.getInternalAtPres();

        final Term modTerm = loopSpec.getModifies(
                services.getTypeConverter().getHeapLDT().getHeap(), loopSpec.getInternalSelfTerm(),
                atPres, services);

        /*
         * NOTE (DS, 2019-11-25): Actually, we should also consider anonymize in the
         * presence of allLocs, but that was use much in non-AE-KeY for anonymizing the
         * heap only, therefore it will probably break existing proofs...
         */
        final UniqueArrayList<AbstractUpdateLoc> locs = AbstractUpdateFactory
                .abstrUpdateLocsFromUnionTerm(modTerm, Optional.of(ec), services).stream()
                .filter(loc -> loc instanceof SkolemLoc).map(HasToLoc::new)
                .collect(Collectors.toCollection(() -> new UniqueArrayList<>()));

        if (locs.isEmpty()) {
            return tb.skip();
        }

        final String newPhsId = tb.newName("anon_LOOP");
        // register fake function to save name
        services.getNamespaces().functions().addSafely(new Function(new Name(newPhsId), Sort.ANY));

        final AbstractStatement as = new AbstractStatement(newPhsId);
        final AbstractUpdate abstrUpd = services.abstractUpdateFactory().getInstance(as, locs, 1);

        // TODO (DS. 2019-11-22): Could/should use an accessibles specification here!
        return tb.abstractUpdate(abstrUpd, new Term[] { tb.allLocs() });
    }

}