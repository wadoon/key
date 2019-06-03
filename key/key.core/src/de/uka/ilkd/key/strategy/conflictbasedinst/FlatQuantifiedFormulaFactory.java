package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;

public class FlatQuantifiedFormulaFactory {

    private Services services;
    private TermBuilder tb;
    private TermFactory tf;

    private FlatQuantifiedFormulaFactory(Services services) {
        this.services = services;
        this.tb = services.getTermBuilder();
        this.tf = services.getTermFactory();
    }

    public static FlatQuantifiedFormula flattenFormula(Term term, Services services) {
        FlatQuantifiedFormulaFactory fqff = new FlatQuantifiedFormulaFactory(services);
        LinkedHashSet<QuantifiableVariable> vars = new LinkedHashSet<>();
        vars.add(term.boundVars().get(0));
        LinkedHashSet<Term> constraints = new LinkedHashSet<>();
        // a formula is ground until the opposite is found
        FlatQuantifiedFormula fqf = new FlatQuantifiedFormula(term.sub(0), vars, constraints, true);
        return fqff.flatten(fqf);
    }

    private FlatQuantifiedFormula flatten(FlatQuantifiedFormula fqf) {
        fqf = flattenSubs(fqf);
        if(isGround(fqf)) return fqf;
        return null;
    }

    private boolean isGround(FlatQuantifiedFormula fqf) {
        return fqf.isGround() && fqf.getTerm().sort() == Sort.FORMULA;
    }

    private FlatQuantifiedFormula flattenSubs(FlatQuantifiedFormula fqf) {
        for(Term sub: fqf.getTerm().subs()) {
            FlatQuantifiedFormula fsub = flatten(new FlatQuantifiedFormula(
                    sub, fqf.getVars(), fqf.getConstraints(), fqf.isGround()));
            combineSubFormula(fqf, fsub);
        }
        return null;
    }

    private void combineSubFormula(FlatQuantifiedFormula fqf,
            FlatQuantifiedFormula fsub) {
        // if a subformula is non-ground, the formula can not be ground
        fqf.setGround(fqf.isGround() && fsub.isGround());
        // add all new quantified variables
        fqf.getVars().addAll(fqf.getVars());

        fqf.getConstraints().addAll(fsub.getConstraints());

    }

    //    private ImmutableSet<QuantifiableVariable> freshVars;
    //    private Term qf;
    //    private QuantifiableVariable qv;
    //    private Term constraints;
    //    private Services services;
    //    private Term flat;
    //    private int cnt;
    //
    //    private FlatQuantifiedFormulaFactory(Term qf, Services services) {
    //        this.qf = qf;
    //        this.qv = qf.boundVars().get(0);
    //        this.services = services;
    //    }
    //
    //    private FlatQuantifiedFormula getFlattenedQuantifiedFormula() {
    //        cnt = 0;
    //        freshVars = DefaultImmutableSet.nil();
    //        System.out.println("Starting to replace from " + qf.toString());
    //        flat = flatten(qf).getTerm();
    //        System.out.println("Flattened Formula: " + flat.toString());
    //        return new FlatQuantifiedFormula(flat);
    //    }
    //
    //
    //
    //    //    private FlattenResult flatten_old(Term term) {
    //    //        if(isGround(term))  {
    //    //            System.out.println(term.toString() + " is Ground, return.");
    //    //            return term;
    //    //        }
    //    //        if(term.op() instanceof QuantifiableVariable) {
    //    //            QuantifiableVariable qv = (QuantifiableVariable) term.op();
    //    //            if(freshVars.contains(qv)) {
    //    //                System.out.println(term.toString() + " is fresh var, return.");
    //    //                return term;
    //    //            }else {
    //    //                Term fresh = freshVariable();
    //    //                addConstraint(term, fresh);
    //    //                System.out.println(term.toString() + " is qv, replace with " + fresh.toString());
    //    //                return fresh;
    //    //            }
    //    //        }
    //    //        if(isMinimalFunction(term)) {
    //    //            Term fresh = freshVariable();
    //    //            addConstraint(term, fresh);
    //    //            System.out.println(term.toString() + " is minimal, replace with " + fresh.toString());
    //    //            return fresh;
    //    //        }
    //    //        System.out.println(term.toString() + " is nothing, replace subs.");
    //    //        ImmutableSet<Term> replacedSubs = DefaultImmutableSet.nil();
    //    //        for(Term sub : term.subs()) {
    //    //            replacedSubs = replacedSubs.add(flatten(sub));
    //    //        }
    //    //        Term[] replacedSubsArray = new Term[replacedSubs.size()];
    //    //        term = services.getTermFactory().createTerm(term.op(), replacedSubs.toArray(replacedSubsArray));
    //    //        return flatten(term);
    //    //    }
    //
    //    private FlattenResult flatten(Term term) {
    //
    //        // the result will be ground if the term is ground
    //        boolean ground = isGround(term);
    //
    //        // if the term has subterms
    //        if(term.subs().size() != 0) {
    //            // flatten all subterms first
    //            FlattenResult fr = flattenSubs(term.op(), term.subs());
    //            // the result is not ground if one subterm is not ground
    //            ground = ground && fr.isGround();
    //            // the term we work with is now the term with flattened subterms
    //            term = fr.getTerm();
    //        }
    //
    //        // if the term is still ground (that means all subterms are also ground)
    //        //if(ground)
    //
    //
    //        return null;
    //    }
    //
    //    private FlattenResult flattenSubs(Operator op, ImmutableArray<Term> subs) {
    //        boolean ground = true;
    //        Term[] flatSubs = new Term[subs.size()];
    //        for(int i = 0; i < subs.size(); i++) {
    //            FlattenResult flatSub = flatten(subs.get(i));
    //            ground = ground && flatSub.isGround();
    //            flatSubs[i] = flatSub.getTerm();
    //        }
    //        return new FlattenResult(
    //                services.getTermFactory().createTerm(op, flatSubs),
    //                ground);
    //    }
    //
    //    private boolean isMinimalFunction(Term term) {
    //        System.out.println(term.op() + " is Function? " + (term.op() instanceof Function));
    //        return (term.op() instanceof Function)
    //                && areFreshVarsOrQuantifiedVar(term.subs());
    //    }
    //
    //    private Term freshVariable() {
    //        QuantifiableVariable fresh = new LogicVariable(new Name(qv.name().toString() + "_" + cnt), qv.sort());
    //        cnt++;
    //        // TODO services.getTermBuilder().newName(baseName)
    //        freshVars = freshVars.add(fresh);
    //        // TODO services.getTermBuilder().var(v)
    //        return services.getTermFactory().createTerm(fresh);
    //    }
    //
    //    public static FlatQuantifiedFormula flatten(Term term, Services services) {
    //        System.out.println("Flatten: " + term.toString());
    //        assert(term.op() == Quantifier.ALL) : "Can only flatten all-quantified formulas";
    //        FlatQuantifiedFormulaFactory qff = new FlatQuantifiedFormulaFactory(term, services);
    //        return qff.getFlattenedQuantifiedFormula();
    //    }
    //
    //    private void addConstraint(Term constraint, Term fresh) {
    //        assert fresh.op() instanceof QuantifiableVariable : "Can only add constraint when fresh term is a variable";
    //        // constraint: equals(fresh, term)
    //        constraint = services.getTermBuilder().equals(
    //                fresh,
    //                constraint);
    //        // constraint: all[S:fresh](equals(fresh, term))
    //        constraint = services.getTermBuilder().all((QuantifiableVariable)fresh.op(), constraint);
    //        System.out.println("Adding constraint: " + constraint.toString());
    //        if(constraints == null) {
    //            constraints = constraint;
    //        }else {
    //            constraints = services.getTermBuilder().and(constraint, constraints);
    //        }
    //    }
    //
    //    private static boolean isGround(Term term) {
    //        return term.freeVars().size() == 0 && term.boundVars().size() == 0;
    //    }
    //
    //    private boolean areFreshVarsOrQuantifiedVar(ImmutableArray<Term> terms) {
    //        for(Term term: terms) {
    //            System.out.println("Fresh or Quant: " + ProofSaver.printTerm(term, services));
    //            if(term.op() instanceof LogicVariable) {
    //                LogicVariable var = (LogicVariable)term.op();
    //                if(!freshVars.contains(var) && !var.equals(qv)) {
    //                    System.out.println(term.toString() + " is not fresh nor qv.");
    //                    return false;
    //                }
    //            }else {
    //                return false;
    //            }
    //        }
    //        return true;
    //    }
    //
    //    private class FlattenResult {
    //        private Term term;
    //        private boolean ground;
    //
    //        public FlattenResult(Term term, boolean ground) {
    //            this.term = term;
    //            this.ground = ground;
    //        }
    //
    //        public Term getTerm() {
    //            return this.term;
    //        }
    //
    //        public boolean isGround() {
    //            return ground;
    //        }
    //    }

}
