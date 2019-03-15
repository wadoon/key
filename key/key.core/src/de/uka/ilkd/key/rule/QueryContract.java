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

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Vector;


/**
 *
 * TODO: document
 *
 *  Not for different heaps
 *
 *  Not for static queries.
 *
 * @author Mattias Ulbrich
 */
public class QueryContract implements BuiltInRule {

	public static final QueryContract INSTANCE = new QueryContract();

	private static final int DEFAULT_MAP_SIZE = 200;

	private static Name QUERY_DEF_NAME = new Name("Query Contract");

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        if (pio == null) {
            return false;
        }

        Term term = pio.subTerm();
        Operator op = term.op();

        if (!(op instanceof IProgramMethod)) {
            return false;
        }

        return true;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return true;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new DefaultBuiltInRuleApp(this, pos);
    }

	@Override
	public ImmutableList<Goal> apply(Goal goal, Services services,
									 RuleApp ruleApp) {

        TermBuilder tb = services.getTermBuilder();

        PosInOccurrence pio = ruleApp.posInOccurrence();
        Term query = pio.subTerm();
        IProgramMethod pm = (IProgramMethod)query.op();
        boolean isStatic = pm.isStatic();

        Term heap = query.sub(0);   // XXX what about two_state, no_state?
        Term receiver = isStatic ? null : query.sub(1);
        ImmutableList<Term> params = query.subs().toImmutableList().take(isStatic ? 1 : 2);
        KeYJavaType throwableClass = services.getJavaInfo().getTypeByClassName("java.lang.Throwable");
        Function excSymbol = new Function(new Name(tb.newName("exc")), throwableClass.getSort());
        Term exc = services.getTermFactory().createTerm(excSymbol);

        final KeYJavaType kjt = pm.getContainerType();

        final List<LocationVariable> heapContext =
                HeapContext.getModHeaps(goal.proof().getServices(), false/* XXX inst.transaction*/);

        Map<LocationVariable, Term> heapTerms = new LinkedHashMap<LocationVariable,Term>();
        for(LocationVariable h : heapContext) {
            heapTerms.put(h, tb.var(h));
        }

        // new goal
        ImmutableList<Goal> newGoal = goal.split(1);
        Goal g = newGoal.head();

        ImmutableSet<FunctionalOperationContract> contracts = services.getSpecificationRepository().getOperationContracts(kjt, pm, Modality.DIA);
        for (FunctionalOperationContract contract : contracts) {
            if (contract.getMod() == null /*strictly pureXXX*/) {
                continue;
            }

            contract.getExc();
            Map<Term, Term> m = contract.getReplaceMap(heapTerms, receiver, params, query, exc, Collections.emptyMap(), services);
            OpReplacer r = new OpReplacer(m, services.getTermFactory());

            Term pre = r.replace(contract.getPre());
            Term post = r.replace(contract.getPost());
            Term ass = services.getTermBuilder().imp(pre, post);

            g.addFormula(new SequentFormula(ass), true, true);
        }

		return newGoal;
	}

    @Override
    public Name name() {
        return QUERY_DEF_NAME;
    }

    @Override
    public String displayName() {
        return QUERY_DEF_NAME.toString();
    }

    @Override
    public String toString() {
        return displayName();
    }
}