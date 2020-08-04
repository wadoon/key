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

package de.uka.ilkd.key.speclang.jml.translation;

import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractionPredicate;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.declaration.modifier.Private;
import de.uka.ilkd.key.java.declaration.modifier.Protected;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.logic.label.OriginTermLabel.SpecType;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.njml.JmlFacade;
import de.uka.ilkd.key.njml.JmlIO;
import de.uka.ilkd.key.njml.JmlParser;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import de.uka.ilkd.key.rule.merge.procedures.MergeByIfThenElse;
import de.uka.ilkd.key.rule.merge.procedures.MergeWithPredicateAbstraction;
import de.uka.ilkd.key.rule.merge.procedures.ParametricMergeProcedure;
import de.uka.ilkd.key.rule.merge.procedures.UnparametricMergeProcedure;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.speclang.jml.JMLInfoExtractor;
import de.uka.ilkd.key.speclang.jml.JMLSpecExtractor;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.speclang.translation.SLWarningException;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import de.uka.ilkd.key.util.mergerule.MergeParamsSpec;
import org.antlr.v4.runtime.ParserRuleContext;
import org.jetbrains.annotations.NotNull;
import org.key_project.util.collection.*;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import static java.lang.String.format;

/**
 * A factory for creating class invariants and operation contracts from textual JML specifications.
 * This is the public interface to the jml.translation package.
 */
public class JMLSpecFactory {

    protected final de.uka.ilkd.key.logic.TermBuilder tb;
    protected final de.uka.ilkd.key.java.Services services;
    protected final ContractFactory cf;
    private int invCounter;
    /**
     * Used to check that there is only one represents clause per type and field.
     */
    private final Set<Pair<KeYJavaType, IObserverFunction>> modelFields;
    private JmlIO jmlIo = new JmlIO();


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------
    public JMLSpecFactory(Services services) {
        assert services != null;
        this.services = services;
        this.tb = services.getTermBuilder();
        cf = new ContractFactory(services);
        modelFields = new LinkedHashSet<>();
        jmlIo.services(services);
    }

    private static Map<LocationVariable, Term> createAtPres(
            final ImmutableList<LocationVariable> paramVars,
            final ImmutableList<LocationVariable> allHeaps, final TermBuilder tb) {
        Map<LocationVariable, Term> atPres = new LinkedHashMap<>();
        for (LocationVariable heap : allHeaps) {
            atPres.put(heap, tb.var(tb.heapAtPreVar(heap + "AtPre", heap.sort(), false)));
        }
        for (LocationVariable param : paramVars) {
            // TODO rename heapAtPreVar
            atPres.put(param, tb.var(tb.heapAtPreVar(param + "AtPre", param.sort(), false)));
        }
        return atPres;
    }

    private static Map<LocationVariable, Term> translateToTermInvariants(IProgramMethod pm,
                                                                         Map<String, ImmutableList<ParserRuleContext>> originalInvariants,
                                                                         ProgramVariable selfVar, ImmutableList<ProgramVariable> allVars,
                                                                         final ImmutableList<LocationVariable> allHeaps,
                                                                         final Map<LocationVariable, Term> atPres, final Services services, final TermBuilder tb)
            throws SLTranslationException {
        Map<LocationVariable, Term> invariants = new LinkedHashMap<LocationVariable, Term>();
        for (LocationVariable heap : allHeaps) {
            Term invariant;
            ImmutableList<ParserRuleContext> originalInvariant
                    = originalInvariants.get(heap.name().toString());
            if (originalInvariant == null || originalInvariant.isEmpty()) {
                invariant = null;
            } else {
                invariant = tb.tt();
                for (ParserRuleContext expr : originalInvariant) {
                    Term translated = JmlIO.translateTerm(expr, pm.getContainerType(), selfVar,
                            allVars, null, null, atPres, atPres,
                            SpecType.LOOP_INVARIANT, services);
                    invariant = tb.andSC(invariant, tb.convertToFormula(translated));
                }
            }
            invariants.put(heap, invariant);
        }
        return invariants;
    }

    private static Map<LocationVariable, Term> translateToTermFreeInvariants(IProgramMethod pm,
                                                                             Map<String, ImmutableList<ParserRuleContext>> originalFreeInvariants,
                                                                             ProgramVariable selfVar, ImmutableList<ProgramVariable> allVars,
                                                                             final ImmutableList<LocationVariable> allHeaps,
                                                                             final Map<LocationVariable, Term> atPres, final Services services, final TermBuilder tb)
            throws SLTranslationException {
        Map<LocationVariable, Term> freeInvariants = new LinkedHashMap<LocationVariable, Term>();
        for (LocationVariable heap : allHeaps) {
            Term freeInvariant;
            ImmutableList<ParserRuleContext> originalFreeInvariant
                    = originalFreeInvariants.get(heap.name().toString());
            if (originalFreeInvariant == null || originalFreeInvariant.isEmpty()) {
                freeInvariant = null;
            } else {
                freeInvariant = tb.tt();
                for (ParserRuleContext expr : originalFreeInvariant) {
                    Term translated = JmlIO.translateTerm(expr, pm.getContainerType(), selfVar,
                            allVars, null, null, atPres, atPres,
                            SpecType.LOOP_INVARIANT_FREE, services);
                    freeInvariant = tb.andSC(freeInvariant, tb.convertToFormula(translated));
                }
            }
            freeInvariants.put(heap, freeInvariant);
        }
        return freeInvariants;
    }

    private ImmutableSet<Contract> createInformationFlowContracts(ContractClauses clauses,
                                                                  IProgramMethod pm, ProgramVariableCollection progVars) {
        LocationVariable heap = services.getTypeConverter().getHeapLDT().getHeap();

        // create contracts
        ImmutableSet<Contract> symbDatas = DefaultImmutableSet.nil();
        if (clauses.infFlowSpecs != null && !clauses.infFlowSpecs.isEmpty()) {
            if (clauses.diverges.equals(tb.ff())) {
                InformationFlowContract symbData = cf.createInformationFlowContract(
                        pm.getContainerType(), pm, pm.getContainerType(), Modality.DIA,
                        clauses.requires.get(heap), clauses.requiresFree.get(heap),
                        clauses.measuredBy,
                        clauses.assignables.get(heap), !clauses.hasMod.get(heap), progVars,
                        clauses.accessibles.get(heap), clauses.infFlowSpecs, false);
                symbDatas = symbDatas.add(symbData);
            } else if (clauses.diverges.equals(tb.tt())) {
                InformationFlowContract symbData = cf.createInformationFlowContract(
                        pm.getContainerType(), pm, pm.getContainerType(), Modality.BOX,
                        clauses.requires.get(heap), clauses.requiresFree.get(heap),
                        clauses.measuredBy,
                        clauses.assignables.get(heap), !clauses.hasMod.get(heap), progVars,
                        clauses.accessibles.get(heap), clauses.infFlowSpecs, false);
                symbDatas = symbDatas.add(symbData);
            } else {
                InformationFlowContract symbData1 = cf.createInformationFlowContract(
                        pm.getContainerType(), pm, pm.getContainerType(), Modality.DIA,
                        tb.and(clauses.requires.get(heap), tb.not(clauses.diverges)),
                        clauses.requiresFree.get(heap),
                        clauses.measuredBy, clauses.assignables.get(heap),
                        !clauses.hasMod.get(heap), progVars, clauses.accessibles.get(heap),
                        clauses.infFlowSpecs, false);
                InformationFlowContract symbData2 = cf.createInformationFlowContract(
                        pm.getContainerType(), pm, pm.getContainerType(), Modality.BOX,
                        clauses.requires.get(heap), clauses.requiresFree.get(heap),
                        clauses.measuredBy,
                        clauses.assignables.get(heap), !clauses.hasMod.get(heap), progVars,
                        clauses.accessibles.get(heap), clauses.infFlowSpecs, false);
                symbDatas = symbDatas.add(symbData1).add(symbData2);
            }
        }
        return symbDatas;
    }

    // -------------------------------------------------------------------------
    // internal classes
    // -------------------------------------------------------------------------
    public static class ContractClauses {
        public ImmutableList<Term> abbreviations = ImmutableSLList.nil();
        public Map<LocationVariable, Term> requires = new LinkedHashMap<>();
        public Map<LocationVariable, Term> requiresFree = new LinkedHashMap<>();
        public Term measuredBy;
        public Term decreases;
        public Map<LocationVariable, Term> assignables = new LinkedHashMap<>();
        public Map<ProgramVariable, Term> accessibles = new LinkedHashMap<>();
        public Map<LocationVariable, Term> ensures = new LinkedHashMap<>();
        public Map<LocationVariable, Term> ensuresFree = new LinkedHashMap<>();
        public Map<LocationVariable, Term> axioms = new LinkedHashMap<>();
        public Term signals;
        public Term signalsOnly;
        public Term diverges;
        public Map<Label, Term> breaks;
        public Map<Label, Term> continues;
        public Term returns;
        public Map<LocationVariable, Boolean> hasMod = new LinkedHashMap<>();
        public ImmutableList<InfFlowSpec> infFlowSpecs;

        public void clear() {
        }
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    protected String getDefaultInvName(String name, KeYJavaType kjt) {
        invCounter++;
        if (name == null) {
            return "JML class invariant nr " + (invCounter - 1) + " in " + kjt.getName();
        } else {
            return "JML class invariant \"" + name + "\" in " + kjt.getName() + " (nr "
                    + (invCounter - 1) + ")";
        }
    }

    private String getInicName() {
        return "JML initially clause";
    }

    private String getContractName(IProgramMethod programMethod, Behavior behavior) {
        return "JML " + behavior.toString() + "operation contract";
    }

    /**
     * Collects local variables of the passed statement that are visible for the passed loop.
     * Returns null if the loop has not been found.
     */
    private ImmutableList<ProgramVariable> collectLocalVariables(StatementContainer sc,
                                                                 LoopStatement loop) {
        ImmutableList<ProgramVariable> result = ImmutableSLList.nil();
        for (int i = 0, m = sc.getStatementCount(); i < m; i++) {
            Statement s = sc.getStatementAt(i);

            if (s instanceof For) {
                ImmutableArray<VariableSpecification> avs = ((For) s).getVariablesInScope();
                for (int j = 0, n = avs.size(); j < n; j++) {
                    VariableSpecification vs = avs.get(j);
                    ProgramVariable pv = (ProgramVariable) vs.getProgramVariable();
                    result = result.prepend(pv);
                }
            }

            if (s == loop) {
                return result;
            } else if (s instanceof LocalVariableDeclaration) {
                ImmutableArray<VariableSpecification> vars
                        = ((LocalVariableDeclaration) s).getVariables();
                for (int j = 0, n = vars.size(); j < n; j++) {
                    ProgramVariable pv = (ProgramVariable) vars.get(j).getProgramVariable();
                    result = result.prepend(pv);
                }
            } else if (s instanceof StatementContainer) {
                ImmutableList<ProgramVariable> lpv
                        = collectLocalVariables((StatementContainer) s, loop);
                if (lpv != null) {
                    result = result.prepend(lpv);
                    return result;
                }
            } else if (s instanceof BranchStatement) {
                BranchStatement bs = (BranchStatement) s;
                for (int j = 0, n = bs.getBranchCount(); j < n; j++) {
                    ImmutableList<ProgramVariable> lpv
                            = collectLocalVariables(bs.getBranchAt(j), loop);
                    if (lpv != null) {
                        result = result.prepend(lpv);
                        return result;
                    }
                }
            }
        }
        return null;
    }

    private VisibilityModifier getVisibility(TextualJMLConstruct textualConstruct) {
        for (String mod : textualConstruct.getMods()) {
            if (mod.equals("private")) {
                return new Private();
            } else if (mod.equals("protected")) {
                return new Protected();
            } else if (mod.equals("public")) {
                return new Public();
            }
        }
        return null;
    }

    /*
     * Create variables for self, parameters, result, exception, and the map for atPre-Functions
     */

    public ProgramVariableCollection createProgramVariables(IProgramMethod pm) {
        ProgramVariableCollection progVar = new ProgramVariableCollection();
        progVar.selfVar = tb.selfVar(pm, pm.getContainerType(), false);
        progVar.paramVars = tb.paramVars(pm, false);
        progVar.resultVar = tb.resultVar(pm, false);
        progVar.excVar = pm.isModel() ? null : tb.excVar(pm, false);

        progVar.atPreVars = new LinkedHashMap<>();
        progVar.atPres = new LinkedHashMap<>();
        for (LocationVariable h : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            LocationVariable lv = tb.heapAtPreVar(h + "AtPre", h.sort(), false);
            progVar.atPreVars.put(h, lv);
            progVar.atPres.put(h, tb.var(lv));
        }
        return progVar;
    }

    private ContractClauses translateJMLClauses(IProgramMethod pm,
                                                TextualJMLSpecCase textualSpecCase, ProgramVariableCollection progVars,
                                                Behavior originalBehavior) throws SLTranslationException {
        ContractClauses clauses = new ContractClauses();
        final LocationVariable savedHeap = services.getTypeConverter().getHeapLDT().getSavedHeap();

        clauses.abbreviations = registerAbbreviationVariables(textualSpecCase,
                pm.getContainerType(), progVars, clauses);

        clauses.measuredBy = translateMeasuredBy(pm, progVars.selfVar, progVars.paramVars,
                textualSpecCase.getMeasuredBy());

        clauses.decreases = translateDecreases(pm, progVars.selfVar, progVars.paramVars,
                progVars.atPres, progVars.atBefores, textualSpecCase.getDecreases());

        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            translateAssignable(pm, progVars, heap, savedHeap,
                    textualSpecCase.getAssignable(heap.name().toString()), clauses);
            translateRequires(pm, progVars, heap, savedHeap,
                    textualSpecCase.getRequires(heap.name().toString()),
                    textualSpecCase.getRequiresFree(heap.name().toString()), clauses);
            translateEnsures(pm, progVars, heap, savedHeap,
                    textualSpecCase.getEnsures(heap.name().toString()),
                    textualSpecCase.getEnsuresFree(heap.name().toString()), clauses,
                    originalBehavior);
            translateAxioms(pm, progVars, heap, textualSpecCase.getAxioms(heap.name().toString()),
                    clauses, originalBehavior);
            translateAccessible(pm, progVars, heap, progVars.atPreVars.get(heap), savedHeap,
                    textualSpecCase.getAccessible(heap.name().toString()),
                    textualSpecCase.getAccessible(heap.name().toString() + "AtPre"), clauses);
        }
        clauses.signals = translateSignals(pm, progVars.selfVar, progVars.paramVars,
                progVars.resultVar, progVars.excVar, progVars.atPres, progVars.atBefores,
                originalBehavior, textualSpecCase.getSignals());
        clauses.signalsOnly = translateSignalsOnly(pm, progVars.excVar, originalBehavior,
                textualSpecCase.getSignalsOnly());
        clauses.diverges = translateOrClauses(pm, progVars.selfVar, progVars.paramVars,
                textualSpecCase.getDiverges());
        clauses.breaks = translateBreaks(pm, progVars.selfVar, progVars.paramVars,
                progVars.resultVar, progVars.excVar, progVars.atPres, progVars.atBefores,
                originalBehavior, textualSpecCase.getBreaks());
        clauses.continues = translateContinues(pm, progVars.selfVar, progVars.paramVars,
                progVars.resultVar, progVars.excVar, progVars.atPres, progVars.atBefores,
                originalBehavior, textualSpecCase.getContinues());
        clauses.returns = translateReturns(pm, progVars.selfVar, progVars.paramVars,
                progVars.resultVar, progVars.excVar, progVars.atPres, progVars.atBefores,
                originalBehavior, textualSpecCase.getReturns());
        clauses.infFlowSpecs = translateInfFlowSpecClauses(pm, progVars.selfVar, progVars.paramVars,
                progVars.resultVar, progVars.excVar, textualSpecCase.getInfFlowSpecs());
        return clauses;
    }

    private void translateAccessible(IProgramMethod pm, ProgramVariableCollection progVars,
                                     LocationVariable heap, ProgramVariable heapAtPre, final LocationVariable savedHeap,
                                     ImmutableList<ParserRuleContext> accessible,
                                     ImmutableList<ParserRuleContext> accessiblePre, ContractClauses clauses)
            throws SLTranslationException {
        if (heap == savedHeap && accessible.isEmpty()) {
            clauses.accessibles.put(heap, null);
            clauses.accessibles.put(heapAtPre, null);
        } else {
            clauses.accessibles.put(heap, translateAssignable(pm, progVars.selfVar,
                    progVars.paramVars, progVars.atPres, progVars.atBefores, accessible));
            clauses.accessibles.put(heapAtPre, translateAssignable(pm, progVars.selfVar,
                    progVars.paramVars, progVars.atPres, progVars.atBefores, accessiblePre));
        }
    }

    private void translateAxioms(IProgramMethod pm, ProgramVariableCollection progVars,
                                 LocationVariable heap, ImmutableList<ParserRuleContext> axioms, ContractClauses clauses,
                                 Behavior originalBehavior) throws SLTranslationException {
        if (axioms.isEmpty()) {
            clauses.axioms.put(heap, null);
        } else {
            clauses.axioms.put(heap,
                    translateEnsures(pm, progVars.selfVar, progVars.paramVars, progVars.resultVar,
                            progVars.excVar, progVars.atPres, progVars.atBefores, originalBehavior,
                            axioms));
        }
    }

    private void translateEnsures(IProgramMethod pm, ProgramVariableCollection progVars,
                                  LocationVariable heap, final LocationVariable savedHeap,
                                  ImmutableList<ParserRuleContext> ensures, ImmutableList<ParserRuleContext> ensuresFree,
                                  ContractClauses clauses, Behavior originalBehavior) throws SLTranslationException {
        if (heap == savedHeap && ensures.isEmpty()) {
            clauses.ensures.put(heap, null);
        } else {
            clauses.ensures.put(heap,
                    translateEnsures(pm, progVars.selfVar, progVars.paramVars, progVars.resultVar,
                            progVars.excVar, progVars.atPres, progVars.atBefores, originalBehavior,
                            ensures));
        }

        if (heap == savedHeap && ensuresFree.isEmpty()) {
            clauses.ensuresFree.put(heap, null);
        } else {
            clauses.ensuresFree.put(heap,
                    translateAndClauses(pm, progVars.selfVar, progVars.paramVars,
                            progVars.resultVar, progVars.excVar, progVars.atPres,
                            progVars.atBefores, ensuresFree, SpecType.ENSURES_FREE));
        }
    }

    private void translateRequires(IProgramMethod pm, ProgramVariableCollection progVars,
                                   LocationVariable heap, final LocationVariable savedHeap,
                                   final ImmutableList<ParserRuleContext> requires,
                                   final ImmutableList<ParserRuleContext> requiresFree, ContractClauses clauses)
            throws SLTranslationException {
        if (heap == savedHeap && requires.isEmpty()) {
            clauses.requires.put(heap, null);
        } else {
            clauses.requires.put(heap, translateAndClauses(pm, progVars.selfVar, progVars.paramVars,
                    null, null, progVars.atPres, progVars.atBefores, requires, SpecType.REQUIRES));
        }
        if (heap == savedHeap && requiresFree.isEmpty()) {
            clauses.requiresFree.put(heap, null);
        } else {
            clauses.requiresFree.put(heap,
                    translateAndClauses(pm, progVars.selfVar, progVars.paramVars, null, null,
                            progVars.atPres, progVars.atBefores, requiresFree,
                            SpecType.REQUIRES_FREE));
        }
    }

    private void translateAssignable(IProgramMethod pm, ProgramVariableCollection progVars,
                                     LocationVariable heap, final LocationVariable savedHeap,
                                     final ImmutableList<ParserRuleContext> mod, ContractClauses clauses)
            throws SLTranslationException {
        clauses.hasMod.put(heap,
                !translateStrictlyPure(pm, progVars.selfVar, progVars.paramVars, mod));
        if (heap == savedHeap && mod.isEmpty()) {
            clauses.assignables.put(heap, null);
        } else if (!clauses.hasMod.get(heap)) {
            final ImmutableList<ParserRuleContext> assignableNothing = ImmutableSLList
                    .<ParserRuleContext>nil().append(getAssignableNothing());
            clauses.assignables.put(heap, translateAssignable(pm, progVars.selfVar,
                    progVars.paramVars, progVars.atPres, progVars.atBefores, assignableNothing));
        } else {
            clauses.assignables.put(heap, translateAssignable(pm, progVars.selfVar,
                    progVars.paramVars, progVars.atPres, progVars.atBefores, mod));
        }
    }

    @NotNull
    private ParserRuleContext getAssignableNothing() {
        return JmlFacade.parseClause("assignable \\nothing;");
    }

    /**
     * register abbreviations in contracts (aka. old clauses). creates update terms.
     *
     * @throws SLTranslationException
     */
    private ImmutableList<Term> registerAbbreviationVariables(TextualJMLSpecCase textualSpecCase,
                                                              KeYJavaType inClass, ProgramVariableCollection progVars, ContractClauses clauses)
            throws SLTranslationException {
        for (Triple<ParserRuleContext, ParserRuleContext, ParserRuleContext> abbrv : textualSpecCase.getAbbreviations()) {
            final KeYJavaType abbrKJT = services.getJavaInfo().getKeYJavaType(abbrv.first.getText());
            final ProgramElementName abbrVarName = new ProgramElementName(abbrv.second.getText());
            final LocationVariable abbrVar = new LocationVariable(abbrVarName, abbrKJT, true, true);
            assert abbrVar.isGhost() : "specification parameter not ghost";
            services.getNamespaces().programVariables().addSafely(abbrVar);
            progVars.paramVars = progVars.paramVars.append(abbrVar); // treat as
            // (ghost)
            // parameter
            final Term rhs = JmlIO.translateTerm(
                    abbrv.third, inClass, progVars.selfVar,
                    progVars.paramVars, progVars.resultVar, progVars.excVar, progVars.atPres,
                    progVars.atBefores, null, services);
            clauses.abbreviations
                    = clauses.abbreviations.append(tb.elementary(tb.var(abbrVar), rhs));
        }
        return clauses.abbreviations;
    }

    private ImmutableList<InfFlowSpec> translateInfFlowSpecClauses(IProgramMethod pm,
                                                                   ProgramVariable selfVar,
                                                                   ImmutableList<ProgramVariable> paramVars,
                                                                   ProgramVariable resultVar, ProgramVariable excVar,
                                                                   ImmutableList<ParserRuleContext> originalClauses) throws SLTranslationException {
        if (originalClauses.isEmpty()) {
            return ImmutableSLList.nil();
        } else {
            ImmutableList<InfFlowSpec> result = ImmutableSLList.nil();
            for (ParserRuleContext expr : originalClauses) {
                InfFlowSpec translated = jmlIo
                        .classType(pm.getContainerType())
                        .selfVar(selfVar)
                        .parameters(paramVars)
                        .resultVariable(resultVar)
                        .exceptionVariable(excVar)
                        .translateInfFlow(expr);
                if (translated != null) {
                    result = result.append(translated);
                }
            }
            return result;
        }
    }

    /**
     * Clauses are expected to be conjoined in a right-associative way, i.e. A & (B & ( C (...&
     * N))). When using auto induction with lemmas, then A will be used as a lemma for B, A & B will
     * be used as a lemma for C and so on. This mimics the Isabelle-style of proving.
     */
    private Term translateAndClauses(IProgramMethod pm, ProgramVariable selfVar,
                                     ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
                                     ProgramVariable excVar, Map<LocationVariable, Term> atPres,
                                     Map<LocationVariable, Term> atBefores, ImmutableList<ParserRuleContext> originalClauses,
                                     SpecType specType)
            throws SLTranslationException {
        // The array is used to invert the order in which the elements are read.
        ParserRuleContext[] array = new ParserRuleContext[originalClauses.size()];
        originalClauses.toArray(array);

        Term result = tb.tt();
        for (int i = array.length - 1; i >= 0; i--) {
            Term translated = JmlIO.translateTerm(array[i], pm.getContainerType(), selfVar,
                    paramVars, resultVar, excVar, atPres, atBefores,
                    specType, services);
            Term translatedFormula = tb.convertToFormula(translated);
            result = tb.andSC(translatedFormula, result);
        }
        return result;
    }

    private Term translateOrClauses(IProgramMethod pm, ProgramVariable selfVar,
                                    ImmutableList<ProgramVariable> paramVars,
                                    ImmutableList<ParserRuleContext> originalClauses) throws SLTranslationException {
        Term result = tb.ff();
        for (ParserRuleContext expr : originalClauses) {
            Term translated = jmlIo.classType(pm.getContainerType())
                    .selfVar(selfVar)
                    .parameters(paramVars)
                    .translateTerm(expr);
            result = tb.orSC(result, tb.convertToFormula(translated));
        }
        return result;
    }

    private Term translateUnionClauses(IProgramMethod pm, ProgramVariable selfVar,
                                       ImmutableList<ProgramVariable> paramVars, Map<LocationVariable, Term> atPres,
                                       Map<LocationVariable, Term> atBefores, ImmutableList<ParserRuleContext> originalClauses,
                                       SpecType specType)
            throws SLTranslationException {
        Term result = tb.empty();
        for (ParserRuleContext expr : originalClauses) {
            if (expr == null) continue;//TODO trace
            Term translated = JmlIO.translateTerm(expr, pm.getContainerType(), selfVar,
                    paramVars, null, null, atPres, atBefores, specType, services);

            // less than nothing is marked by some special term;
            if (translated.equalsModIrrelevantTermLabels(tb.strictlyNothing())) {
                if (originalClauses.size() > 1) {
                    throw new SLTranslationException(
                            "\"assignable \\less_than_nothing\" does not go with other "
                                    + "assignable clauses (even if they declare the same).",
                            expr);
                }
                return tb.empty();
            }

            result = tb.union(result, translated);
        }

        return result;
    }

    private Map<Label, Term> translateBreaks(IProgramMethod pm, ProgramVariable selfVar,
                                             ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
                                             ProgramVariable excVar, Map<LocationVariable, Term> atPres,
                                             Map<LocationVariable, Term> atBefores, Behavior originalBehavior,
                                             ImmutableList<ParserRuleContext> originalClauses) throws SLTranslationException {
        ParserRuleContext[] array = new ParserRuleContext[originalClauses.size()];
        originalClauses.toArray(array);
        Map<Label, Term> result = new LinkedHashMap<Label, Term>();
        for (int i = array.length - 1; i >= 0; i--) {
            Pair<Label, Term> translation = JmlIO.translateLabeledClause(array[i], pm.getContainerType(),
                    selfVar, paramVars, resultVar, excVar, atPres, atBefores,
                    SpecType.BREAKS, services);
            result.put(translation.first, translation.second);
        }
        return result;
    }

    private Map<Label, Term> translateContinues(IProgramMethod pm, ProgramVariable selfVar,
                                                ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
                                                ProgramVariable excVar, Map<LocationVariable, Term> atPres,
                                                Map<LocationVariable, Term> atBefores, Behavior originalBehavior,
                                                ImmutableList<ParserRuleContext> originalClauses) throws SLTranslationException {
        ParserRuleContext[] array = new ParserRuleContext[originalClauses.size()];
        originalClauses.toArray(array);
        Map<Label, Term> result = new LinkedHashMap<Label, Term>();
        for (int i = array.length - 1; i >= 0; i--) {
            Pair<Label, Term> translation = JmlIO.translateLabeledClause(array[i], pm.getContainerType(),
                    selfVar, paramVars, resultVar, excVar, atPres, atBefores,
                    SpecType.CONTINUES, services);
            result.put(translation.first, translation.second);
        }
        return result;
    }

    private Term translateReturns(IProgramMethod pm, ProgramVariable selfVar,
                                  ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
                                  ProgramVariable excVar, Map<LocationVariable, Term> atPres,
                                  Map<LocationVariable, Term> atBefores, Behavior originalBehavior,
                                  ImmutableList<ParserRuleContext> originalClauses) throws SLTranslationException {
        if (originalBehavior == Behavior.NORMAL_BEHAVIOR) {
            assert originalClauses.isEmpty();
            return tb.ff();
        } else {
            return translateAndClauses(pm, selfVar, paramVars, resultVar, excVar, atPres, atBefores,
                    originalClauses, SpecType.RETURNS);
        }
    }

    private Term translateSignals(IProgramMethod pm, ProgramVariable selfVar,
                                  ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
                                  ProgramVariable excVar, Map<LocationVariable, Term> atPres,
                                  Map<LocationVariable, Term> atBefores, Behavior originalBehavior,
                                  ImmutableList<ParserRuleContext> originalClauses) throws SLTranslationException {
        if (originalBehavior == Behavior.NORMAL_BEHAVIOR) {
            assert originalClauses.isEmpty();
            return tb.ff();
        } else {
            return translateAndClauses(pm, selfVar, paramVars, resultVar, excVar, atPres, atBefores,
                    originalClauses, SpecType.SIGNALS);
        }
    }

    private Term translateSignalsOnly(IProgramMethod pm, ProgramVariable excVar,
                                      Behavior originalBehavior, ImmutableList<ParserRuleContext> originalClauses)
            throws SLTranslationException {
        return translateSignals(pm, null, null, null, excVar, null, null, originalBehavior,
                originalClauses);
    }

    private Term translateEnsures(IProgramMethod pm, ProgramVariable selfVar,
                                  ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
                                  ProgramVariable excVar, Map<LocationVariable, Term> atPres,
                                  Map<LocationVariable, Term> atBefores, Behavior originalBehavior,
                                  ImmutableList<ParserRuleContext> originalClauses) throws SLTranslationException {
        if (originalBehavior == Behavior.EXCEPTIONAL_BEHAVIOR) {
            assert originalClauses.isEmpty();
            return tb.ff();
        } else {
            return translateAndClauses(pm, selfVar, paramVars, resultVar, excVar, atPres, atBefores,
                    originalClauses, SpecType.ENSURES);
        }
    }

    @SuppressWarnings("unused")
    private Term translateAccessible(IProgramMethod pm, ProgramVariable selfVar,
                                     ImmutableList<ProgramVariable> paramVars, Map<LocationVariable, Term> atPres,
                                     Map<LocationVariable, Term> atBefores, ImmutableList<ParserRuleContext> originalClauses)
            throws SLTranslationException {
        if (originalClauses.isEmpty()) {
            return tb.allLocs();
        } else {
            return translateUnionClauses(pm, selfVar, paramVars, atPres, atBefores,
                    originalClauses, SpecType.ACCESSIBLE);
        }
    }

    private Term translateAssignable(IProgramMethod pm, ProgramVariable selfVar,
                                     ImmutableList<ProgramVariable> paramVars, Map<LocationVariable, Term> atPres,
                                     Map<LocationVariable, Term> atBefores, ImmutableList<ParserRuleContext> originalClauses)
            throws SLTranslationException {

        if (originalClauses.isEmpty()) {
            return tb.allLocs();
        } else {
            return translateUnionClauses(pm, selfVar, paramVars, atPres, atBefores,
                    originalClauses, SpecType.ASSIGNABLE);
        }
    }

    private boolean translateStrictlyPure(IProgramMethod pm, ProgramVariable selfVar,
                                          ImmutableList<ProgramVariable> paramVars,
                                          ImmutableList<ParserRuleContext> assignableClauses) throws SLTranslationException {

        for (ParserRuleContext expr : assignableClauses) {
            if (expr == null) continue;//TODO trace
            Term translated = jmlIo
                    .classType(pm.getContainerType())
                    .selfVar(selfVar)
                    .parameters(paramVars)
                    .translateTerm(expr);

            // less than nothing is marked by some special term;
            if (translated.equalsModIrrelevantTermLabels(tb.strictlyNothing())) {
                return true;
            }
        }

        return false;
    }

    private Term translateMeasuredBy(IProgramMethod pm, ProgramVariable selfVar,
                                     ImmutableList<ProgramVariable> paramVars,
                                     ImmutableList<ParserRuleContext> originalMeasuredBy) throws SLTranslationException {
        Term measuredBy = null;
        if (!originalMeasuredBy.isEmpty()) {
            for (ParserRuleContext expr : originalMeasuredBy) {
                Term translated = jmlIo
                        .classType(pm.getContainerType())
                        .selfVar(selfVar)
                        .parameters(paramVars)
                        .translateTerm(expr);
                if (measuredBy == null) {
                    measuredBy = translated;
                } else {
                    measuredBy = tb.pair(measuredBy, translated);
                }
            }
        }
        return measuredBy;
    }

    private Term translateDecreases(IProgramMethod pm, ProgramVariable selfVar,
                                    ImmutableList<ProgramVariable> paramVars, Map<LocationVariable, Term> atPres,
                                    Map<LocationVariable, Term> atBefores,
                                    ImmutableList<ParserRuleContext> originalDecreases) throws SLTranslationException {
        Term decreases = null;
        if (!originalDecreases.isEmpty()) {
            for (ParserRuleContext expr : originalDecreases) {
                Term translated = JmlIO.translateTerm(expr, pm.getContainerType(), selfVar,
                        paramVars, null, null, atPres, atBefores,
                        SpecType.DECREASES, services);
                if (decreases == null) {
                    decreases = translated;
                } else {
                    decreases = tb.pair(decreases, translated);
                }
            }
        }
        return decreases;
    }

    public String generateName(IProgramMethod pm, TextualJMLSpecCase textualSpecCase,
                               Behavior originalBehavior) {
        String customName = textualSpecCase.getName();
        return generateName(pm, originalBehavior, customName);
    }

    public String generateName(IProgramMethod pm, Behavior originalBehavior, String customName) {
        String name = ((!(customName == null) && customName.length() > 0) ? customName
                : getContractName(pm, originalBehavior));
        return name;
    }

    private Map<LocationVariable, Term> generatePostCondition(ProgramVariableCollection progVars,
                                                              ContractClauses clauses, Behavior originalBehavior) {
        Map<LocationVariable, Term> result = new LinkedHashMap<LocationVariable, Term>();
        if (progVars.excVar == null) { // Model methods do not have exceptions
            for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                if (clauses.ensures.get(heap) != null) {
                    Term post = tb.convertToFormula(clauses.ensures.get(heap));
                    result.put(heap, post);
                }
            }
        } else {
            for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                if (clauses.ensures.get(heap) != null) {
                    Term excNull = tb.addLabelToAllSubs(
                            (tb.label(tb.equals(tb.var(progVars.excVar), tb.NULL()),
                                    ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL)),
                            new OriginTermLabel(new Origin(SpecType.ENSURES)));
                    Term post1 = (originalBehavior == Behavior.NORMAL_BEHAVIOR
                            ? tb.convertToFormula(clauses.ensures.get(heap))
                            : tb.imp(excNull, tb.convertToFormula(clauses.ensures.get(heap))));
                    Term post2 = (originalBehavior == Behavior.EXCEPTIONAL_BEHAVIOR
                            ? tb.and(tb.convertToFormula(clauses.signals),
                            tb.convertToFormula(clauses.signalsOnly))
                            : tb.imp(tb.not(excNull), tb.and(tb.convertToFormula(clauses.signals),
                            tb.convertToFormula(clauses.signalsOnly))));

                    Term post = heap == services.getTypeConverter().getHeapLDT().getHeap()
                            ? tb.and(post1, post2)
                            : post1;

                    result.put(heap, post);
                } else {
                    if (clauses.assignables.get(heap) != null) {
                        result.put(heap, tb.tt());
                    }
                }
            }
        }
        return result;
    }

    private Map<LocationVariable, Term> generateRepresentsAxioms(ProgramVariableCollection progVars,
                                                                 ContractClauses clauses, Behavior originalBehavior) {
        Map<LocationVariable, Term> result = new LinkedHashMap<LocationVariable, Term>();
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            if (clauses.axioms.get(heap) != null) {
                result.put(heap, tb.convertToFormula(clauses.axioms.get(heap)));
            }
        }
        return result;
    }

    /**
     * Generate functional operation contracts.
     *
     * @param name     base name of the contract (does not have to be unique)
     * @param pm       the IProgramMethod to which the contract belongs
     * @param progVars pre-generated collection of variables for the receiver object, operation
     *                 parameters, operation result, thrown exception and the pre-heap
     * @param clauses  pre-translated JML clauses
     * @return operation contracts including new functional operation contracts
     */
    public ImmutableSet<Contract> createFunctionalOperationContracts(String name,
                                                                     IProgramMethod pm, ProgramVariableCollection progVars, ContractClauses clauses,
                                                                     Map<LocationVariable, Term> posts, Map<LocationVariable, Term> axioms) {
        ImmutableSet<Contract> result = DefaultImmutableSet.nil();

        Term abbrvLhs = null;
        if (!clauses.abbreviations.isEmpty()) {
            abbrvLhs = tb.sequential(clauses.abbreviations);
        }

        // requires
        Map<LocationVariable, Term> pres = new LinkedHashMap<LocationVariable, Term>();
        for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            if (clauses.requires.get(heap) != null) {
                Term pre = tb.convertToFormula(clauses.requires.get(heap));
                pres.put(heap, pre);
            } else {
                if (clauses.assignables.get(heap) != null) {
                    pres.put(heap, tb.tt());
                }
            }
        }

        // diverges
        if (clauses.diverges.equals(tb.ff())) {
            // create diamond modality contract
            FunctionalOperationContract contract = cf.func(name, pm, true, pres,
                    clauses.requiresFree, clauses.measuredBy, posts, clauses.ensuresFree, axioms,
                    clauses.assignables, clauses.accessibles, clauses.hasMod, progVars);
            contract = cf.addGlobalDefs(contract, abbrvLhs);
            result = result.add(contract);
        } else if (clauses.diverges.equals(tb.tt())) {
            // create box modality contract
            FunctionalOperationContract contract = cf.func(name, pm, false, pres,
                    clauses.requiresFree, clauses.measuredBy, posts, clauses.ensuresFree, axioms,
                    clauses.assignables, clauses.accessibles, clauses.hasMod, progVars);
            contract = cf.addGlobalDefs(contract, abbrvLhs);
            result = result.add(contract);
        } else {
            // create two contracts for each diamond and box modality
            for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                if (clauses.requires.get(heap) != null) {
                    pres.put(heap, tb.andSC(pres.get(heap),
                            tb.not(tb.convertToFormula(clauses.diverges))));
                    break;
                }
            }
            FunctionalOperationContract contract1 = cf.func(name, pm, true, pres,
                    clauses.requiresFree, clauses.measuredBy, posts, clauses.ensuresFree, axioms,
                    clauses.assignables, clauses.accessibles, clauses.hasMod, progVars);
            contract1 = cf.addGlobalDefs(contract1, abbrvLhs);
            FunctionalOperationContract contract2 = cf.func(name, pm, false, clauses.requires,
                    clauses.requiresFree, clauses.measuredBy, posts, clauses.ensuresFree, axioms,
                    clauses.assignables, clauses.accessibles, clauses.hasMod, progVars);
            contract2 = cf.addGlobalDefs(contract2, abbrvLhs);
            result = result.add(contract1).add(contract2);
        }
        return result;
    }

    /**
     * Generate dependency operation contract out of the JML accessible clause.
     *
     * @param pm       the IProgramMethod to which the contract belongs
     * @param progVars collection of variables for the receiver object, operation parameters, operation
     *                 result, thrown exception and the pre-heap
     * @param clauses  pre-translated JML clauses
     * @return operation contracts including a new dependency contract
     */
    private ImmutableSet<Contract> createDependencyOperationContract(IProgramMethod pm,
                                                                     ProgramVariableCollection progVars, ContractClauses clauses) {
        ImmutableSet<Contract> result = DefaultImmutableSet.nil();

        Term abbrvLhs = null;
        if (!clauses.abbreviations.isEmpty()) {
            abbrvLhs = tb.sequential(clauses.abbreviations);
        }

        boolean createContract = true;
        for (LocationVariable heap : HeapContext.getModHeaps(services, false)) {
            if (clauses.accessibles.get(heap).equalsModRenaming(tb.allLocs())) {
                createContract = false;
                break;
            }
            if (pm.isModel() && pm.getStateCount() > 1) {
                if (clauses.accessibles.get(progVars.atPreVars.get(heap))
                        .equalsModRenaming(tb.allLocs())) {
                    createContract = false;
                    break;
                }
            } else if (pm.isModel() && pm.getStateCount() == 0) {
                createContract = false;
                break;
            }
        }
        if (createContract) {
            assert (progVars.selfVar == null) == pm.isStatic();
            Map<LocationVariable, Term> pres = new LinkedHashMap<LocationVariable, Term>();
            for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
                if (clauses.requires.get(heap) != null) {
                    final Term pre = tb.convertToFormula(clauses.requires.get(heap));
                    pres.put(heap, pre);
                }
            }
            final Contract depContract = cf.dep(pm.getContainerType(), pm, pm.getContainerType(),
                    pres, clauses.measuredBy, clauses.accessibles, progVars.selfVar,
                    progVars.paramVars, progVars.atPreVars, abbrvLhs);
            result = result.add(depContract);
        }
        return result;
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------
    public ClassInvariant createJMLClassInvariant(
            @NotNull KeYJavaType kjt, VisibilityModifier visibility,
            boolean isStatic, @NotNull ParserRuleContext originalInv) throws SLTranslationException {
        assert kjt != null;
        assert originalInv != null;

        // create variable for self
        ProgramVariable selfVar = isStatic ? null : tb.selfVar(kjt, false);

        // translateToTerm expression
        final Term inv0 = jmlIo
                .classType(kjt)
                .selfVar(selfVar)
                .translateTerm(originalInv);
        Term inv = tb.convertToFormula(inv0);
        // create invariant
        String name = getDefaultInvName(null, kjt);
        return new ClassInvariantImpl(name, name, kjt, visibility, inv, selfVar);
    }

    public ClassInvariant createJMLClassInvariant(KeYJavaType kjt, TextualJMLClassInv textualInv)
            throws SLTranslationException {
        // check whether the invariant is static
        final ImmutableList<String> mods = textualInv.getMods();
        final boolean isStatic = (mods.contains("static") || // modifier
                // "static"
                // in an interface "static" is the default (see Sect. 2.5 of the
                // reference manual)
                (services.getJavaInfo().isInterface(kjt) && !mods.contains("instance")));

        // create variable for self
        ProgramVariable selfVar = isStatic ? null : tb.selfVar(kjt, false);

        // translateToTerm expression
        final Term inv0 = jmlIo
                .classType(kjt)
                .selfVar(selfVar)
                .translateTerm(textualInv.getInv());
        Term inv = tb.convertToFormula(inv0);
        // create invariant
        String name = getDefaultInvName(null, kjt);
        String display = getDefaultInvName(textualInv.getName(), kjt);
        return new ClassInvariantImpl(name, display, kjt, getVisibility(textualInv), inv, selfVar);
    }

    public InitiallyClause createJMLInitiallyClause(KeYJavaType kjt, VisibilityModifier visibility,
                                                    ParserRuleContext original) throws SLTranslationException {
        assert kjt != null;
        assert original != null;

        // create variable for self
        ProgramVariable selfVar = tb.selfVar(kjt, false);

        // translateToTerm expression
        final Term inv0 = jmlIo
                .classType(kjt)
                .selfVar(selfVar)
                .translateTerm(original);

        Term inv = tb.convertToFormula(inv0);

        // create invariant
        String name = getInicName();
        InitiallyClauseImpl res = new InitiallyClauseImpl(name, name, kjt, new Public(), inv, selfVar, original);
        return res;

    }

    public InitiallyClause createJMLInitiallyClause(KeYJavaType kjt, TextualJMLInitially textualInv)
            throws SLTranslationException {
        return createJMLInitiallyClause(kjt, getVisibility(textualInv), textualInv.getInv());
    }

    @SuppressWarnings("unchecked")
    public ClassAxiom createJMLRepresents(KeYJavaType kjt, VisibilityModifier visibility,
                                          ParserRuleContext originalRep, boolean isStatic) throws SLTranslationException {
        assert kjt != null;
        assert originalRep != null;

        // create variable for self
        final ProgramVariable selfVar = isStatic ? null : tb.selfVar(kjt, false);

        // translateToTerm expression
        final Pair<IObserverFunction, Term> rep = jmlIo.translateRepresents(originalRep);
        // represents clauses must be unique per type
        for (Pair<KeYJavaType, IObserverFunction> p : modelFields) {
            if (p.first.equals(kjt) && p.second.equals(rep.first)) {
                throw new SLTranslationException(
                        "JML represents clauses must occur uniquely per type and target.", originalRep);
            }
        }
        modelFields.add(new Pair<KeYJavaType, IObserverFunction>(kjt, rep.first));
        Term repFormula = tb.convertToFormula(rep.second);
        // create class axiom
        return new RepresentsAxiom("JML represents clause for " + rep.first.name().toString(),
                rep.first, kjt, visibility, null, repFormula, selfVar,
                ImmutableSLList.nil(), null);
    }

    @SuppressWarnings("unchecked")
    public ClassAxiom createJMLRepresents(KeYJavaType kjt, TextualJMLRepresents textualRep)
            throws SLTranslationException {
        boolean isStatic = textualRep.getMods().contains("static");
        // create variable for self
        final ProgramVariable selfVar = isStatic ? null : tb.selfVar(kjt, false);

        // translateToTerm expression
        final ParserRuleContext clause = textualRep.getRepresents();
        final Pair<IObserverFunction, Term> rep = jmlIo.translateRepresents(clause);
        // check whether there already is a represents clause
        if (!modelFields.add(new Pair<>(kjt, rep.first))) {
            throw new SLWarningException("JML represents clauses must occur uniquely per "
                    + "type and target." + "\nAll but one are ignored.",
                    clause.start.getTokenSource().getSourceName(),
                    new Position(clause.start.getLine(), clause.start.getCharPositionInLine()));
        }
        // create class axiom
        String name = "JML represents clause for " + rep.first.name().toString();
        String displayName = textualRep.getName() == null ? name
                : "JML represents clause \"" + textualRep.getName() + "\" for " + rep.first.name();
        Term repFormula = tb.convertToFormula(rep.second);
        return new RepresentsAxiom(name, displayName, rep.first, kjt, getVisibility(textualRep),
                null, repFormula, selfVar, ImmutableSLList.nil(), null);
    }

    /**
     * Creates a class axiom from a textual JML representation. As JML axioms are always without
     * modifiers, they are implicitly non-static and public.
     *
     * @param kjt     the type where the axiom is declared
     * @param textual textual representation
     * @return created {@link ClassAxiom}
     * @throws SLTranslationException translation exception
     */
    public ClassAxiom createJMLClassAxiom(KeYJavaType kjt, TextualJMLClassAxiom textual) throws SLTranslationException {
        ParserRuleContext originalRep = textual.getAxiom();
        assert kjt != null;
        assert originalRep != null;

        // create variable for self
        final ProgramVariable selfVar = tb.selfVar(kjt, false);

        // translate expression
        final Term inv0 = jmlIo
                .classType(kjt)
                .selfVar(selfVar)
                .translateTerm(originalRep);
        final Term ax = tb.convertToFormula(inv0);

        // create class axiom
        String name = "class axiom in " + kjt.getFullName();
        String displayName = textual.getName() == null ? name
                : "class axiom \"" + textual.getName() + "\" in " + kjt.getFullName();
        return new ClassAxiomImpl(name, displayName, kjt, new Public(), ax, selfVar);
    }

    public Contract createJMLDependencyContract(KeYJavaType kjt, LocationVariable targetHeap,
                                                ParserRuleContext originalDep) throws SLTranslationException {
        assert kjt != null;
        assert originalDep != null;

        // create variable for self
        ProgramVariable selfVar = tb.selfVar(kjt, false);

        // translateToTerm expression
        Triple<IObserverFunction, Term, Term> dep = JmlIO.translateDependencyContract(originalDep, kjt,
                selfVar, null, null, null, null, null, services);
        return cf.dep(kjt, targetHeap, dep, dep.first.isStatic() ? null : selfVar);
    }

    public Contract createJMLDependencyContract(KeYJavaType kjt, TextualJMLDepends textualDep)
            throws SLTranslationException {
        ParserRuleContext dep = null;
        LocationVariable targetHeap = null;
        for (LocationVariable heap : HeapContext.getModHeaps(services, false)) {
            dep = textualDep.getDepends(heap.name().toString()).head();
            if (dep != null) {
                targetHeap = heap;
                break;
            }
        }
        assert dep != null;
        assert targetHeap != null;
        return createJMLDependencyContract(kjt, targetHeap, dep);
    }

    /**
     * Creates operation contracts out of the passed JML specification.
     *
     * @param pm              corresponding program method
     * @param textualSpecCase textual representation of spec
     * @return created JML operation contracts
     * @throws SLTranslationException a translation exception
     */
    public ImmutableSet<Contract> createJMLOperationContracts(IProgramMethod pm,
                                                              TextualJMLSpecCase textualSpecCase) throws SLTranslationException {
        assert pm != null;
        assert textualSpecCase != null;

        Behavior originalBehavior
                = pm.isModel() ? Behavior.MODEL_BEHAVIOR : textualSpecCase.getBehavior();

        String name = generateName(pm, textualSpecCase, originalBehavior);

        // prepare program variables, translateToTerm JML clauses and generate
        // post
        // condition
        ProgramVariableCollection progVars = createProgramVariables(pm);
        ContractClauses clauses
                = translateJMLClauses(pm, textualSpecCase, progVars, originalBehavior);
        Map<LocationVariable, Term> posts
                = generatePostCondition(progVars, clauses, originalBehavior);
        Map<LocationVariable, Term> axioms
                = generateRepresentsAxioms(progVars, clauses, originalBehavior);

        // create contracts
        ImmutableSet<Contract> result = DefaultImmutableSet.nil();
        result = result.union(createInformationFlowContracts(clauses, pm, progVars));
        result = result.union(
                createFunctionalOperationContracts(name, pm, progVars, clauses, posts, axioms));
        result = result.union(createDependencyOperationContract(pm, progVars, clauses));

        return result;
    }

    public ImmutableSet<MergeContract> createJMLMergeContracts(final IProgramMethod method,
                                                               final MergePointStatement mps, final TextualJMLMergePointDecl mergePointDecl,
                                                               ImmutableList<ProgramVariable> methodParams)
            throws SLTranslationException {
        final JmlParser.Merge_point_statementContext ctx = mergePointDecl.getMergeProc();

        final String mergeProcStr = ctx.proc != null
                ? MergeByIfThenElse.instance().toString() //default merge procedure
                : ctx.proc.getText().replaceAll("\"", "");

        /*final String mergeParamsStr = mergePointDecl.getMergeParams() == null ? null
                : mergePointDecl.getMergeParams().text;
        final ParserRuleContext mergeParamsParseStr = mergeParamsStr == null ? null
                : JmlFacade.parseClause("merge_params " + mergeParamsStr);*/
        MergeProcedure mergeProc = MergeProcedure.getProcedureByName(mergeProcStr);
        if (mergeProc == null) {
            throw new SLTranslationException(format("Unknown merge procedure: \"%s\"", mergeProcStr),
                    mergePointDecl.getSourceFileName(), mergePointDecl.getApproxPosition());
        }
        ImmutableSet<MergeContract> result = DefaultImmutableSet.nil();

        KeYJavaType kjt = method.getContainerType();
        if (mergeProc instanceof UnparametricMergeProcedure) {
            final UnparameterizedMergeContract unparameterizedMergeContract
                    = new UnparameterizedMergeContract(mergeProc, mps, kjt);
            result = result.add(unparameterizedMergeContract);
        } else if (mergeProc instanceof ParametricMergeProcedure) { // arguments expected looking for params
            if (!(mergeProc instanceof MergeWithPredicateAbstraction))
                throw new IllegalStateException(
                        "Currently, MergeWithPredicateAbstraction(Factory) is the only supported ParametricMergeProcedure");

            // @formatter:off
            // Expected merge params structure:
            // merge_params <LATTICE-TYPE>: (<TYPE> <PLACHOLDER>) -> {<JML-FORMULA>}
            // @formatter:on
            final ProgramVariableCollection progVars = createProgramVariables(method);

            // Determine the variables in "\old(...)" expressions and register
            // remembrance variables for them
            final ImmutableList<LocationVariable> params = method.collectParameters();
            final Map<LocationVariable, Term> atPres = new LinkedHashMap<>();
            final ImmutableList<LocationVariable> allHeaps
                    = services.getTypeConverter().getHeapLDT().getAllHeaps();
            final String atPrePrefix = "AtPre";
            allHeaps.forEach(heap -> atPres.put(heap, tb.var(tb.heapAtPreVar(heap + atPrePrefix, heap.sort(), false))));
            params.forEach(param -> atPres.put(param,
                    tb.var(tb.heapAtPreVar(param + atPrePrefix, param.sort(), false))));

            final MergeParamsSpec specs = jmlIo
                    .classType(kjt)
                    .selfVar(progVars.selfVar)
                    .parameters(append(ImmutableSLList.nil(), params))
                    .resultVariable(progVars.resultVar)
                    .exceptionVariable(progVars.excVar)
                    .atPres(atPres)
                    .translateMergeParams(ctx.mergeparamsspec());

            result = result.add(new PredicateAbstractionMergeContract(mps, atPres, kjt,
                    specs.getLatticeType(),
                    StreamSupport.stream(specs.getPredicates().spliterator(), true).map(
                            t -> AbstractionPredicate.create(t, specs.getPlaceholder(), services))
                            .collect(Collectors
                                    .toCollection(ArrayList::new))));
        } else {
            throw new IllegalStateException(
                    "MergeProcedures should either be an UnparametricMergeProcedure or a ParametricMergeProcedure");
        }
        return result;
    }

    /**
     * Creates a set of block contracts for a block from a textual specification case.
     *
     * @param method            the method containing the block.
     * @param labels            all labels belonging to the block.
     * @param block             the block which the block contracts belong to.
     * @param specificationCase the textual specification case.
     * @return a set of block contracts for a block from a textual specification case.
     * @throws SLTranslationException translation exception
     */
    public ImmutableSet<BlockContract> createJMLBlockContracts(final IProgramMethod method,
                                                               final List<Label> labels, final StatementBlock block,
                                                               final TextualJMLSpecCase specificationCase) throws SLTranslationException {
        if (specificationCase.isLoopContract()) {
            return DefaultImmutableSet.nil();
        }

        final Behavior behavior = specificationCase.getBehavior();
        final BlockContract.Variables variables
                = BlockContract.Variables.create(block, labels, method, services);
        final ProgramVariableCollection programVariables
                = createProgramVariables(method, block, variables);
        final ContractClauses clauses
                = translateJMLClauses(method, specificationCase, programVariables, behavior);
        return new BlockContractImpl.Creator("JML " + behavior + "block contract", block, labels,
                method, behavior, variables, clauses.requires, clauses.measuredBy, clauses.ensures,
                clauses.infFlowSpecs, clauses.breaks, clauses.continues, clauses.returns,
                clauses.signals, clauses.signalsOnly, clauses.diverges, clauses.assignables,
                clauses.hasMod, services).create();
    }

    /**
     * Creates a set of loop contracts for a loop from a textual specification case.
     *
     * @param method            the method containing the block.
     * @param labels            all labels belonging to the block.
     * @param loop              the loop which the loop contracts belong to.
     * @param specificationCase the textual specification case.
     * @return a set of loop contracts for a block from a textual specification case.
     * @throws SLTranslationException a translation exception
     */
    public ImmutableSet<LoopContract> createJMLLoopContracts(final IProgramMethod method,
                                                             final List<Label> labels, final LoopStatement loop,
                                                             final TextualJMLSpecCase specificationCase) throws SLTranslationException {
        if (!specificationCase.isLoopContract()) {
            return DefaultImmutableSet.nil();
        }

        final Behavior behavior = specificationCase.getBehavior();
        final LoopContract.Variables variables
                = LoopContract.Variables.create(loop, labels, method, services);
        final ProgramVariableCollection programVariables
                = createProgramVariables(method, loop, variables);
        final ContractClauses clauses
                = translateJMLClauses(method, specificationCase, programVariables, behavior);
        return new LoopContractImpl.Creator("JML " + behavior + "loop contract", loop, labels,
                method, behavior, variables, clauses.requires, clauses.measuredBy, clauses.ensures,
                clauses.infFlowSpecs, clauses.breaks, clauses.continues, clauses.returns,
                clauses.signals, clauses.signalsOnly, clauses.diverges, clauses.assignables,
                clauses.hasMod, clauses.decreases, services).create();
    }

    /**
     * Creates a set of loop contracts for a block from a textual specification case.
     *
     * @param method            the method containing the block.
     * @param labels            all labels belonging to the block.
     * @param block             the block which the loop contracts belong to.
     * @param specificationCase the textual specification case.
     * @return a set of loop contracts for a block from a textual specification case.
     * @throws SLTranslationException a translation exception
     */
    public ImmutableSet<LoopContract> createJMLLoopContracts(final IProgramMethod method,
                                                             final List<Label> labels, final StatementBlock block,
                                                             final TextualJMLSpecCase specificationCase) throws SLTranslationException {
        if (!specificationCase.isLoopContract()) {
            return DefaultImmutableSet.nil();
        }

        final Behavior behavior = specificationCase.getBehavior();
        final LoopContract.Variables variables
                = LoopContract.Variables.create(block, labels, method, services);
        final ProgramVariableCollection programVariables
                = createProgramVariables(method, block, variables);
        final ContractClauses clauses
                = translateJMLClauses(method, specificationCase, programVariables, behavior);
        return new LoopContractImpl.Creator("JML " + behavior + "loop contract", block, labels,
                method, behavior, variables, clauses.requires, clauses.measuredBy, clauses.ensures,
                clauses.infFlowSpecs, clauses.breaks, clauses.continues, clauses.returns,
                clauses.signals, clauses.signalsOnly, clauses.diverges, clauses.assignables,
                clauses.hasMod, clauses.decreases, services).create();
    }

    /**
     * Creates a program variable collection for a specified block. This collection contains all
     * program variables that occur freely in the block as parameters (i.e., in
     * {@link ProgramVariableCollection#paramVars}).
     *
     * @param method    the method containing the block.
     * @param block     the block.
     * @param variables an instance of {@link AuxiliaryContract.Variables} for the block.
     * @return
     */
    private ProgramVariableCollection createProgramVariables(final IProgramMethod method,
                                                             final JavaStatement block, final BlockContract.Variables variables) {
        final Map<LocationVariable, LocationVariable> remembranceVariables
                = variables.combineRemembranceVariables();
        final Map<LocationVariable, LocationVariable> outerRemembranceVariables
                = variables.combineOuterRemembranceVariables();

        ImmutableList<ProgramVariable> vars;

        SourceElement first = block.getFirstElement();
        while (first instanceof LabeledStatement) {
            first = ((LabeledStatement) first).getBody();
        }

        if (first instanceof For) {
            vars = append(collectLocalVariables(method.getBody(), (For) first),
                    method.collectParameters())
                    .append(collectLocalVariablesVisibleTo(block, method));
        } else {
            vars = append(ImmutableSLList.nil(), method.collectParameters())
                    .append(collectLocalVariablesVisibleTo(block, method));
        }

        return new ProgramVariableCollection(variables.self, vars, variables.result,
                variables.exception, outerRemembranceVariables, termify(outerRemembranceVariables),
                remembranceVariables, termify(remembranceVariables));
    }

    private Map<LocationVariable, Term>
    termify(final Map<LocationVariable, LocationVariable> remembranceVariables) {
        final Map<LocationVariable, Term> result = new LinkedHashMap<>();
        for (Map.Entry<LocationVariable,
                LocationVariable> remembranceVariable : remembranceVariables.entrySet()) {
            result.put(remembranceVariable.getKey(), tb.var(remembranceVariable.getValue()));
        }
        return result;
    }

    protected ImmutableList<ProgramVariable>
    collectLocalVariablesVisibleTo(final Statement statement, final IProgramMethod method) {
        return collectLocalVariablesVisibleTo(statement, method.getBody());
    }

    private ImmutableList<ProgramVariable> collectLocalVariablesVisibleTo(final Statement statement,
                                                                          final StatementContainer container) {
        ImmutableList<ProgramVariable> result = ImmutableSLList.nil();
        final int statementCount = container.getStatementCount();
        for (int i = 0; i < statementCount; i++) {
            final Statement s = container.getStatementAt(i);
            if (s instanceof For) {
                final ImmutableArray<VariableSpecification> variables
                        = ((For) s).getVariablesInScope();
                for (int j = 0; j < variables.size(); j++) {
                    result = result
                            .prepend((ProgramVariable) variables.get(j).getProgramVariable());
                }
            }
            if (s == statement) {
                return result;
            } else if (s instanceof LocalVariableDeclaration) {
                final ImmutableArray<VariableSpecification> variables
                        = ((LocalVariableDeclaration) s).getVariables();
                for (int j = 0; j < variables.size(); j++) {
                    result = result
                            .prepend((ProgramVariable) variables.get(j).getProgramVariable());
                }
            } else if (s instanceof StatementContainer) {
                final ImmutableList<ProgramVariable> visibleLocalVariables
                        = collectLocalVariablesVisibleTo(statement, (StatementContainer) s);
                if (visibleLocalVariables != null) {
                    result = result.prepend(visibleLocalVariables);
                    return result;
                }
            } else if (s instanceof BranchStatement) {
                final BranchStatement branch = (BranchStatement) s;
                final int branchCount = branch.getBranchCount();
                for (int j = 0; j < branchCount; j++) {
                    final ImmutableList<ProgramVariable> visibleLocalVariables
                            = collectLocalVariablesVisibleTo(statement, branch.getBranchAt(j));
                    if (visibleLocalVariables != null) {
                        result = result.prepend(visibleLocalVariables);
                        return result;
                    }
                }
            }
        }
        return null;
    }

    private LoopSpecification createJMLLoopInvariant(IProgramMethod pm, LoopStatement loop,
                                                     Map<String, ImmutableList<ParserRuleContext>> originalInvariants,
                                                     Map<String, ImmutableList<ParserRuleContext>> originalFreeInvariants,
                                                     Map<String, ImmutableList<ParserRuleContext>> originalAssignables,
                                                     ImmutableList<ParserRuleContext> originalInfFlowSpecs, ParserRuleContext originalVariant)
            throws SLTranslationException {
        assert pm != null;
        assert loop != null;
        assert originalInvariants != null;
        assert originalAssignables != null;
        assert originalInfFlowSpecs != null;

        // create variables for self, parameters, other relevant local variables
        // (disguised as parameters to the translator) and the map for
        // atPre-Functions
        ProgramVariable selfVar = tb.selfVar(pm, pm.getContainerType(), false);
        final ImmutableList<LocationVariable> paramVars = pm.collectParameters();
        ProgramVariable resultVar = tb.resultVar(pm, false);
        ProgramVariable excVar = tb.excVar(pm, false); // only for information
        // flow

        final ImmutableList<LocationVariable> allHeaps
                = services.getTypeConverter().getHeapLDT().getAllHeaps();

        final Map<LocationVariable, Term> atPres = createAtPres(paramVars, allHeaps, tb);

        ImmutableList<ProgramVariable> localVars = collectLocalVariables(pm.getBody(), loop);
        ImmutableList<ProgramVariable> allVars = append(localVars, paramVars);

        // translateToTerm invariant
        final Map<LocationVariable, Term> invariants = translateToTermInvariants(pm,
                originalInvariants, selfVar, allVars, allHeaps, atPres, services, tb);

        Map<LocationVariable, Term> freeInvariants = translateToTermFreeInvariants(pm,
                originalFreeInvariants, selfVar, allVars, allHeaps, atPres, services, tb);

        // translateToTerm assignable
        Map<LocationVariable, Term> mods
                = translateToTermAsssignable(pm, selfVar, atPres, allVars, originalAssignables);

        // translateToTerm infFlowSpecs
        Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs
                = translateToTermInfFlowSpecs(pm, selfVar, resultVar, excVar, allVars, allHeaps,
                originalInfFlowSpecs);

        // translateToTerm variant
        Term variant = translateToTermVariant(pm, selfVar, atPres, allVars, originalVariant);

        ImmutableList<Term> localIns = tb.var(MiscTools.getLocalIns(loop, services));
        ImmutableList<Term> localOuts = tb.var(MiscTools.getLocalOuts(loop, services));

        // create loop invariant annotation
        Term selfTerm = selfVar == null ? null : tb.var(selfVar);

        return new LoopSpecImpl(loop, pm, pm.getContainerType(), invariants, freeInvariants, mods,
                infFlowSpecs, variant, selfTerm, localIns, localOuts, atPres);
    }

    private Term translateToTermVariant(IProgramMethod pm, ProgramVariable selfVar,
                                        Map<LocationVariable, Term> atPres, ImmutableList<ProgramVariable> allVars,
                                        ParserRuleContext originalVariant) throws SLTranslationException {
        final Term variant;
        if (originalVariant == null) {
            variant = null;
        } else {
            variant = JmlIO.translateTerm(originalVariant, pm.getContainerType(),
                    selfVar, allVars, null, null, atPres, atPres,
                    SpecType.DECREASES, services);
        }
        return variant;
    }

    private Map<LocationVariable, ImmutableList<InfFlowSpec>> translateToTermInfFlowSpecs(
            IProgramMethod pm, ProgramVariable selfVar, ProgramVariable resultVar,
            ProgramVariable excVar, ImmutableList<ProgramVariable> allVars,
            final ImmutableList<LocationVariable> allHeaps,
            ImmutableList<ParserRuleContext> originalInfFlowSpecs) throws SLTranslationException {
        Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs
                = new LinkedHashMap<>();
        ImmutableList<InfFlowSpec> infFlowSpecTermList;
        final LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
        for (LocationVariable heap : allHeaps) {
            if (!originalInfFlowSpecs.isEmpty() && heap.equals(baseHeap)) {
                infFlowSpecTermList = translateInfFlowSpecClauses(pm, selfVar, allVars, resultVar,
                        excVar, originalInfFlowSpecs);
            } else {
                infFlowSpecTermList = ImmutableSLList.nil();
            }
            infFlowSpecs.put(heap, infFlowSpecTermList);
        }
        return infFlowSpecs;
    }

    private Map<LocationVariable, Term> translateToTermAsssignable(IProgramMethod pm,
                                                                   ProgramVariable selfVar, Map<LocationVariable, Term> atPres,
                                                                   ImmutableList<ProgramVariable> allVars,
                                                                   Map<String, ImmutableList<ParserRuleContext>> originalAssignables)
            throws SLTranslationException {
        Map<LocationVariable, Term> mods = new LinkedHashMap<>();
        for (String h : originalAssignables.keySet()) {
            LocationVariable heap
                    = services.getTypeConverter().getHeapLDT().getHeapForName(new Name(h));
            if (heap == null) {
                continue;
            }
            Term a;
            ImmutableList<ParserRuleContext> as = originalAssignables.get(h);
            if (as.isEmpty()) {
                a = tb.allLocs();
            } else {
                a = tb.empty();
                for (ParserRuleContext expr : as) {
                    Term translated = JmlIO.translateTerm(
                            expr, pm.getContainerType(), selfVar,
                            allVars, null, null, atPres, atPres,
                            SpecType.ASSIGNABLE, services);
                    a = tb.union(a, translated);
                }
            }
            mods.put(heap, a);
        }
        return mods;
    }

    // ImmutableList does not accept lists of subclasses to #append and cannot
    // be lifted without changing the interface.
    // Hence this little helper.
    private ImmutableList<ProgramVariable> append(ImmutableList<ProgramVariable> localVars,
                                                  ImmutableList<LocationVariable> paramVars) {
        ImmutableList<ProgramVariable> result = ImmutableSLList.nil();
        for (LocationVariable param : paramVars) {
            result = result.prepend(param);
        }
        return result.prepend(localVars);
    }

    public LoopSpecification createJMLLoopInvariant(IProgramMethod pm, LoopStatement loop,
                                                    TextualJMLLoopSpec textualLoopSpec) throws SLTranslationException {
        return createJMLLoopInvariant(pm, loop,
                textualLoopSpec.getInvariants(),
                textualLoopSpec.getFreeInvariants(),
                textualLoopSpec.getAssignablesInit(),
                textualLoopSpec.getInfFlowSpecs(),
                textualLoopSpec.getVariant());
    }

    /**
     * Translate initially clause to a contract for the given constructor. Exception is thrown if
     * the methods passed is not a constructor. For an initially clause <tt>ini</tt> the resulting
     * contract looks like:<br>
     * <tt>requires true;<br>ensures ini;<br>signals (Exception) ini;<br>diverges true;</tt>
     *
     * @param ini initially clause
     * @param pm  constructor
     * @return the translated (functional operation) contract
     * @throws SLTranslationException a translation exception
     */
    public FunctionalOperationContract initiallyClauseToContract(InitiallyClause ini, IProgramMethod pm)
            throws SLTranslationException {
        // if (! pm.isConstructor()) throw new SLTranslationException("Initially
        // clauses only apply to constructors, not to method "+pm);
        final ImmutableList<String> mods = ImmutableSLList.<String>nil().append("private");
        final TextualJMLSpecCase specCase = new TextualJMLSpecCase(mods, Behavior.NONE);
        //TODO specCase.addName(ini.getName());
        //TODO specCase.addRequires(createPrecond(pm, ini.getOriginalSpec()));
        //TODO specCase.addEnsures(ini.getOriginalSpec().prepend("\\invariant_for(this) &&"));
        //TODO specCase.addSignals(ini.getOriginalSpec().prepend("\\invariant_for(this) &&"));
        //TODO specCase.addDiverges(new ParserRuleContext("true"));
        ImmutableSet<Contract> resultList = createJMLOperationContracts(pm, specCase);
        assert resultList.size() == 1;
        Contract result = resultList.toArray(new Contract[1])[0];
        assert result instanceof FunctionalOperationContract;
        return ((FunctionalOperationContract) result);
    }

    private ImmutableList<ParserRuleContext> createPrecond(IProgramMethod pm, ParserRuleContext originalSpec) {
        ImmutableList<ParserRuleContext> res = ImmutableSLList.nil();
        // TODO: add static invariant
        for (ParameterDeclaration p : pm.getMethodDeclaration().getParameters()) {
            if (!JMLInfoExtractor.parameterIsNullable(pm, p)) {
                final ImmutableSet<ParserRuleContext> nonNullPositionedString = JMLSpecExtractor.createNonNullPositionedString(
                        p.getVariableSpecification().getName(),
                        p.getVariableSpecification().getProgramVariable().getKeYJavaType(), false,
                        originalSpec.start.getTokenSource().getSourceName(),
                        new Position(originalSpec.start.getLine(), originalSpec.start.getCharPositionInLine()), services);
                res = res.append(nonNullPositionedString);
            }
        }
        return res;
    }
}
