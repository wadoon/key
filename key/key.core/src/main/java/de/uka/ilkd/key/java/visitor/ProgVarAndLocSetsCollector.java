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

import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.LoopContract;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.speclang.MergeContract;

/**
 * Walks through a java AST in depth-left-fist-order. This walker is used
 * collect all LocationVariables and, in the context of abstract execution,
 * LocSet constants in the accessible / assignable clauses of block contracts.
 */
public class ProgVarAndLocSetsCollector extends JavaASTVisitor {
    private final Set<Operator> result = new LinkedHashSet<>();
    private final ProgramVariableCollector delegate;

    /**
     * collects all program variables occurring in the AST <tt>root</tt> using
     * this constructor is equivalent to
     * <tt>ProggramVariableCollector(root, false)</tt>
     *
     * @param root
     *            the ProgramElement which is the root of the AST
     * @param services
     *            the Services object
     */
    public ProgVarAndLocSetsCollector(ProgramElement root, Services services) {
        super(root, services);
        assert services != null;
        this.delegate = new ProgramVariableCollector(root, services);
    }

    @Override
    public void start() {
        walk(root());
    }

    public Set<Operator> result() {
        result.addAll(delegate.result());
        return result;
    }

    @Override
    public String toString() {
        return result.toString();
    }

    @Override
    protected void doDefaultAction(SourceElement x) {
    }

    @Override
    public void performActionOnLocationVariable(LocationVariable x) {
        delegate.performActionOnLocationVariable(x);
    }

    @Override
    public void performActionOnAbstractPlaceholderStatementContract(
            BlockContract x) {
        performActionOnBlockContract(x);
    }

    @Override
    public void performActionOnMergeContract(MergeContract x) {
        delegate.performActionOnMergeContract(x);
    }

    @Override
    public void performActionOnLoopInvariant(LoopSpecification x) {
        delegate.performActionOnLoopInvariant(x);

        final Term selfTerm = x.getInternalSelfTerm();
        final ImmutableList<LocationVariable> allHeaps = //
                services.getTypeConverter().getHeapLDT().getAllHeaps();

        Map<LocationVariable, Term> atPres = x.getInternalAtPres();

        // modifies
        for (LocationVariable heap : allHeaps) {
            addSkolemLocsFromTermToResultDefaultAllLocs(
                    x.getModifies(heap, selfTerm, atPres, services));
        }
    }

    @Override
    public void performActionOnBlockContract(BlockContract x) {
        delegate.performActionOnBlockContract(x);

        final ImmutableList<LocationVariable> allHeaps = //
                services.getTypeConverter().getHeapLDT().getAllHeaps();

        for (LocationVariable heap : allHeaps) {
            addSkolemLocsFromTermToResultDefaultAllLocs(
                    x.getModifiesClause(heap, services));
        }

        for (LocationVariable heap : allHeaps) {
            addSkolemLocsFromTermToResultDefaultAllLocs(
                    x.getAccessibleClause(heap, services));
        }
    }

    @Override
    public void performActionOnLoopContract(LoopContract x) {
        delegate.performActionOnLoopContract(x);

        final ImmutableList<LocationVariable> allHeaps = //
                services.getTypeConverter().getHeapLDT().getAllHeaps();

        for (LocationVariable heap : allHeaps) {
            addSkolemLocsFromTermToResultDefaultAllLocs(
                    x.getModifiesClause(heap, services));
        }

        for (LocationVariable heap : allHeaps) {
            addSkolemLocsFromTermToResultDefaultAllLocs(
                    x.getAccessibleClause(heap, services));
        }
    }

    /**
     * Adds all Skolem loc set constants from the given term to result if any,
     * otherwise, adds the allLocs location.
     *
     * @param extractFrom
     *            The {@link Term} from which to extract.
     */
    private void addSkolemLocsFromTermToResultDefaultAllLocs(
            final Term extractFrom) {
        final Optional<Set<Operator>> maybeLocSetConsts = //
                Optional.ofNullable(extractFrom)
                        .map(this::getSkolemLocSetConstantsFromLocSetUnionTerm);
        maybeLocSetConsts.ifPresent(result::addAll);
        if (!maybeLocSetConsts.isPresent()) {
            result.add(services.getTypeConverter().getLocSetLDT().getAllLocs());
        }
    }

    private Set<Operator> getSkolemLocSetConstantsFromLocSetUnionTerm(
            final Term unionTerm) {
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        assert unionTerm.sort() == locSetLDT.targetSort();

        final OpCollector opColl = new OpCollector();
        unionTerm.execPostOrder(opColl);
        return opColl.ops().stream().filter(Function.class::isInstance)
                .map(Function.class::cast)
                .filter(f -> f.arity() == 0
                        && f.sort() == locSetLDT.targetSort())
                .collect(Collectors.toCollection(LinkedHashSet::new));
    }

}