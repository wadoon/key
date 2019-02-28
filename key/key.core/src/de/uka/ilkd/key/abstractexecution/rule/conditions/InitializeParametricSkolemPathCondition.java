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

package de.uka.ilkd.key.abstractexecution.rule.conditions;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
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
public class InitializeParametricSkolemPathCondition
        implements VariableCondition {
    private final SchemaVariable pathCondSV;
    private final ProgramSV abstrProgSV;

    public InitializeParametricSkolemPathCondition(SchemaVariable pathCondSV,
            ProgramSV abstrProgSV) {
        this.pathCondSV = pathCondSV;
        this.abstrProgSV = abstrProgSV;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        if (svInst.isInstantiated(pathCondSV)) {
            return matchCond;
        }

        final AbstractPlaceholderStatement abstrStmt = (AbstractPlaceholderStatement) svInst
                .getInstantiation(abstrProgSV);

        final TermBuilder tb = services.getTermBuilder();

        /*
         * NOTE (DS, 2019-01-31): We reuse the function symbols because
         * otherwise, there will be different ones around which can, and will,
         * lead to problems, since they should represent the same thing. It will
         * however be problematic if someone decides to introduce such a
         * function symbol elsewhere...
         */
        final String pathCondName = //
                pathCondSV.name().toString() + "_" + abstrStmt.getId();

        final Name funcSymbName = new Name(pathCondName);
        final Namespace<Function> functions = //
                services.getNamespaces().functions();

        Function funcSymb = functions.lookup(funcSymbName);
        if (funcSymb == null) {
            final Sort setSort = //
                    services.getTypeConverter().getSetLDT().targetSort();
            funcSymb = new Function( //
                    funcSymbName, Sort.FORMULA, true, true, setSort);
            functions.add(funcSymb);
        }

        final Term accessibleClause = AbstractExecutionUtils
                .getAccessibleAndAssignableTermsForNoBehaviorContract(abstrStmt,
                        matchCond, services).first;

        final Term pathCond = tb.func(funcSymb, accessibleClause);

        return matchCond
                .setInstantiations(svInst.add(pathCondSV, pathCond, services));
    }

    @Override
    public String toString() {
        final List<SchemaVariable> svs = new ArrayList<>();
        svs.add(pathCondSV);
        svs.add(abstrProgSV);

        final String svsString = svs.stream().map(SchemaVariable::toString)
                .collect(Collectors.joining(", "));

        return String.format(
                "\\varcond (\\initializeParametricSkolemPathCondition(%s))",
                svsString);
    }
}
