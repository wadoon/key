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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Instantiates a parametric skolem path condition for abstract execution. The
 * such generated formula receives one LocSet for its assignable; those are
 * obtained from the block contracts of the {@link AbstractPlaceholderStatement}
 * it is generated for.
 *
 * @author Dominic Steinhöfel
 */
public class InitializeParametricSkolemPathCondition extends
        InitializeParametricSkolemConstructsForAE implements VariableCondition {
    private final SchemaVariable pathCondSV;
    private final ProgramSV abstrProgSV;
    private final ProgramSV excSV;
    private final ProgramSV returnedSV;
    private final ProgramSV resultSV;

    public InitializeParametricSkolemPathCondition(SchemaVariable pathCondSV,
            ProgramSV abstrProgSV, ProgramSV excSV, ProgramSV returnedSV,
            ProgramSV resultSV) {
        this.pathCondSV = pathCondSV;
        this.abstrProgSV = abstrProgSV;
        this.excSV = excSV;
        this.returnedSV = returnedSV;
        this.resultSV = resultSV;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        if (svInst.isInstantiated(pathCondSV)) {
            return matchCond;
        }

        final AbstractPlaceholderStatement abstrStmt =
                (AbstractPlaceholderStatement) svInst
                        .getInstantiation(abstrProgSV);

        final TermBuilder tb = services.getTermBuilder();

        Term accessibleClause = getAccessibleAndAssignableTerms(abstrStmt,
                svInst, services).first;

        for (final ProgramSV furtherSV : new ProgramSV[] { excSV, returnedSV,
                resultSV }) {
            final LocationVariable furtherLV =
                    (LocationVariable) svInst.getInstantiation(furtherSV);
            accessibleClause = tb.union(accessibleClause,
                    tb.singletonPV(tb.var(furtherLV)));
        }

        final String pathCondName = tb.newName(
                pathCondSV.name().toString() + "_" + abstrStmt.getId());
        final Sort locSetSort =
                services.getTypeConverter().getLocSetLDT().targetSort();

        final Term pathCond = tb.func(new Function(new Name(pathCondName),
                Sort.FORMULA, true, false, locSetSort), accessibleClause);

        return matchCond
                .setInstantiations(svInst.add(pathCondSV, pathCond, services));
    }

    @Override
    public String toString() {
        return String.format(
                "\\varcond (\\initializeParametricSkolemPathCondition(%s, %s))",
                pathCondSV, abstrProgSV);
    }
}
