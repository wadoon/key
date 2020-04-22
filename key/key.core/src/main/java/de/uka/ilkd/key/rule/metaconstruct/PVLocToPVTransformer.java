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
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Creates the wellformedness condition for the given anonymizing heap terms if
 * they apply for the current profile and modality type. At least generates the
 * "wellFormed(anon_heap_LOOP)" condition for the anonymized standard heap.
 * 
 * @author Dominic Steinhoefel
 */
public final class PVLocToPVTransformer extends AbstractTermTransformer {

    public PVLocToPVTransformer() {
        super(new Name("#pvLocToPV"), 1);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            GoalLocalSpecificationRepository localSpecRepo, Services services) {
        final Term pvLocTerm = term.sub(0);
        assert pvLocTerm.op() instanceof Function;
        final Function pvLoc = (Function) pvLocTerm.op();
        assert pvLoc.sort() == services.getTypeConverter().getLocSetLDT().getProgVarSort();

        return services.getPvToLocationMapper().getAssociatedVariable(pvLoc)
                .map(services.getTermBuilder()::var).orElseThrow(() -> new RuntimeException(
                        "No program variable associated to this program variable location."));
    }
}