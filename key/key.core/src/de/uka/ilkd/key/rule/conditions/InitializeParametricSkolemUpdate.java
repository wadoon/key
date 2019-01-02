// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.conditions;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.BlockContract;

/**
 * Instantiate a list {@link ProgramSV} with fresh variables of the given type.
 * The length of the list is either taken from the length of another list of
 * schema variables or a numeric constant. The base name for the new variables
 * can be set via a parameter.
 *
 * @author Dominic Steinhöfel
 */
public class InitializeParametricSkolemUpdate implements VariableCondition {
    private final SchemaVariable updateSV;
    private final ProgramSV abstrProgSV;

    public InitializeParametricSkolemUpdate(SchemaVariable updateSV,
            ProgramSV abstrProgSV) {
        this.updateSV = updateSV;
        this.abstrProgSV = abstrProgSV;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        if (svInst.isInstantiated(updateSV)) {
            return matchCond;
        }

        final AbstractPlaceholderStatement abstrStmt =
                (AbstractPlaceholderStatement) svInst
                        .getInstantiation(abstrProgSV);
        final List<BlockContract> contracts = services
                .getSpecificationRepository()
                .getAbstractPlaceholderStatementContracts(abstrStmt).stream()
                .filter(contract -> contract.getBaseName()
                        .equals("JML block contract"))
                /*
                 * We exclude return_behavior etc. here, because from those
                 * contracts we only consider the precondition.
                 */
                .collect(Collectors.toList());

        assert contracts.size() <= 1;

        Term accessibleClause;
        Term assignableClause;

        final TermBuilder tb = services.getTermBuilder();
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final Sort locSetSort = locSetLDT.targetSort();

        final String updateName = tb
                .newName(updateSV.name().toString() + "_" + abstrStmt.getId());

        if (contracts.isEmpty()) {
            accessibleClause = tb.func(locSetLDT.getAllLocs());
            assignableClause = tb.func(locSetLDT.getAllLocs());
        }
        else {
            /*
             * TODO (DS, 2018-12-21): Choose the right contract! There is
             * probably a contract from the other branch with wrong renamings.
             * We somehow have to find the right one. Ideas: (1) Get all PVs
             * from context and choose the contract with most PVs in common, or
             * (2) store a node ID for the contract in ProgVarReplacer when
             * replacing, such that we can get the contract assigned to a node
             * which is an ancestor of this one, or (3) check the Goal-local
             * namespaces such that we choose the contract for which the locals
             * are known. We could also make the contracts goal-local somehow.
             * Option (1) is the ugliest which also might fail, but the other
             * ones require more actions or passing through more parameters wo
             * this method.
             *
             * Below, there is a quick implementation of method (1).
             */

            final LocationVariable heap =
                    services.getTypeConverter().getHeapLDT().getHeap();

            BlockContract contract = null;
            if (contracts.size() > 1) {
                final ProgramVariableCollector pvColl =
                        new ProgramVariableCollector(svInst
                                .getContextInstantiation().contextProgram(),
                                services);
                pvColl.start();
                final Set<LocationVariable> varsInProg = pvColl.result();

                int varsNotInProg = Integer.MAX_VALUE;
                for (BlockContract bc : contracts) {
                    final OpCollector opColl = new OpCollector();
                    bc.getAccessibleClause(heap).execPostOrder(opColl);
                    bc.getAssignable(heap).execPostOrder(opColl);
                    bc.getAssignableNot(heap).execPostOrder(opColl);
                    final int currVarsNotInProg = (int) opColl.ops().stream()
                            .filter(op -> op instanceof LocationVariable)
                            .map(LocationVariable.class::cast)
                            .filter(pv -> !varsInProg.contains(pv)).count();
                    if (currVarsNotInProg < varsNotInProg) {
                        varsNotInProg = currVarsNotInProg;
                        contract = bc;
                    }
                }
            }
            else {
                contract = contracts.iterator().next();
            }

            // final BlockContract contract = contracts.iterator().next();

            accessibleClause = contract.getAccessibleClause(heap);
            assignableClause = contract.getAssignable(heap);

            /*
             * TODO (DS, 2018-12-21): At this point, we might have to check that
             * the accessibles are actually accessible...
             */
        }

        final Term update = tb.func(
                new Function(new Name(updateName), Sort.UPDATE, true, false,
                        locSetSort, locSetSort),
                assignableClause, accessibleClause);

        return matchCond
                .setInstantiations(svInst.add(updateSV, update, services));
    }

    @Override
    public String toString() {
        return String.format(
                "\\varcond (\\initializeParametricSkolemUpdate(%s, %s))",
                updateSV, abstrProgSV);
    }
}
