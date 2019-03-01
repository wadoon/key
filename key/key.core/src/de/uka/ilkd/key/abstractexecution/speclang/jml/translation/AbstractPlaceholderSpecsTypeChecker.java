package de.uka.ilkd.key.abstractexecution.speclang.jml.translation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionUtils;
import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.FieldSpecification;
import de.uka.ilkd.key.java.declaration.VariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory.ContractClauses;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

/**
 * Checks the specifications (currently assignable and accessible clauses) for
 * an abstract placeholder statement for consistency.
 *
 * The concrete rules are:
 * <ol>
 * <li>Variables specified to be accessible/assignable have to be declared in
 * the visible scope of the block or as method parameters</li>
 * <li>Variables specified to be assignable must not be final</li>
 * <li>Fields declared to be accessible/assignable must exist (TODO (DS,
 * 2019-01-04): Fields currently not considered)</li>
 * <li>Fields declared to be assignable must not be final (TODO (DS,
 * 2019-01-04): Fields currently not considered)</li>
 * <li>Skolem constants specified to be accessible/assignable have to be
 * declared in this or a preceding abstract program in the visible scope</li>
 * <li>If the heap (or a field) is specified to be accessible/assignable, the
 * containing method must not be static</li>
 * </ol>
 *
 * @author Dominic Steinhoefel
 */
public class AbstractPlaceholderSpecsTypeChecker {
    private final IProgramMethod method;
    private final StatementBlock block;
    private final Services services;
    private final ContractClauses clauses;
    private final AbstractPlaceholderStatement aps;
    private final TypeConverter typeConverter;

    public AbstractPlaceholderSpecsTypeChecker(IProgramMethod method,
            StatementBlock block, ContractClauses clauses, Services services) {
        assert block.getChildAt(0) instanceof AbstractPlaceholderStatement;

        this.method = method;
        this.aps = (AbstractPlaceholderStatement) block.getChildAt(0);
        this.block = block;
        this.clauses = clauses;
        this.services = services;
        this.typeConverter = services.getTypeConverter();
    }

    public void check() throws SLTranslationException {
        final List<Pair<? extends Operator, Boolean>> declaredOps = //
                getDeclaredOps();

        /* Check that all accessibles are declared */
        final List<Operator> undeclaredAccessedOps = //
                getUndeclaredAccessedOps(declaredOps);

        if (!undeclaredAccessedOps.isEmpty()) {
            throw new SLTranslationException(String.format(
                    "The following locations are specified to be "
                            + "accessible by abstract program %s, but are not declared: %s",
                    aps.getId(),
                    undeclaredAccessedOps.stream().map(Operator::toString)
                            .collect(Collectors.joining(", "))));
        }

        /* Check that all assignables are not declared final before */
        final List<Operator> assignedFinalOps = //
                getAssignedFinalOps(declaredOps);

        if (!assignedFinalOps.isEmpty()) {
            throw new SLTranslationException(String.format(
                    "The following locations are specified to be "
                            + "assignable by abstract program %s, but declared final: %s",
                    aps.getId(),
                    assignedFinalOps.stream().map(Operator::toString)
                            .collect(Collectors.joining(", "))));
        }

        if (method.isStatic()) {
            /* For static methods, the heap may not be assigned or accessed! */

            if (collectElementsOfLocSetTerm(assignablesTerm(),
                    typeConverter.getLocSetLDT().getUnion(), services)
                            .contains(heap())) {
                throw new SLTranslationException(String.format(
                        "Abstract program %s is specified to assign the heap, "
                                + "but containing method %s is declared static.",
                        aps.getId(), method.name()));
            }

            if (collectElementsOfLocSetTerm(accessiblesTerm(),
                    typeConverter.getLocSetLDT().getUnion(), services)
                            .contains(heap())) {
                throw new SLTranslationException(String.format(
                        "Abstract program %s is specified to access the heap, "
                                + "but containing method %s is declared static.",
                        aps.getId(), method.name()));
            }
        }

        /*
         * TODO (DS, 2019-01-04): After adding declare specifications, also take
         * into account declared Skolem method parameters, and make sure that
         * abstract programs can only declare their own locals!
         */
    }

    private LocationVariable heap() {
        return typeConverter.getHeapLDT().getHeap();
    }

    private List<Operator> getUndeclaredAccessedOps(
            List<Pair<? extends Operator, Boolean>> declaredOps) {
        final Set<Operator> collectedOps = collectElementsOfLocSetTerm(
                accessiblesTerm(), typeConverter.getLocSetLDT().getUnion(),
                services);
        return collectedOps.stream().filter(op -> op.arity() == 0).filter(
                op -> !declaredOps.stream().anyMatch(p -> p.first.equals(op)))
                .collect(Collectors.toList());
    }

    private List<Operator> getAssignedFinalOps(
            List<Pair<? extends Operator, Boolean>> declaredOps) {
        final Set<Operator> collectedOps = collectElementsOfLocSetTerm(
                assignablesTerm(), typeConverter.getLocSetLDT().getUnion(),
                services);
        return collectedOps.stream().filter(op -> op.arity() == 0)
                .filter(op -> declaredOps.stream()
                        .anyMatch(p -> p.first.equals(op) && p.second))
                .collect(Collectors.toList());
    }

    private Term declaresTerm() {
        return clauses.declares.get(heap());
    }

    private Term assignablesTerm() {
        return clauses.assignables.get(heap());
    }

    private Term accessiblesTerm() {
        return clauses.accessibles.get(heap());
    }

    private List<Pair<? extends Operator, Boolean>> getDeclaredOps() {
        final List<Pair<? extends Operator, Boolean>> declaredOps = new ArrayList<>();

        collectDeclaredOpsFromProgram(declaredOps);
        collectDeclaredOpsFromDeclaresTerm(declaredOps);
        collectParameters(declaredOps);
        collectFields(declaredOps);
        collectDeclaredSkolemLocSetsFromMethodContract(declaredOps);
        addDeclaredDefaults(declaredOps);

        return declaredOps;
    }

    private void collectDeclaredOpsFromDeclaresTerm(
            final List<Pair<? extends Operator, Boolean>> declaredOps) {
        declaredOps.addAll( //
                extractDeclaredSkolemLocSetConsts(declaresTerm()));
    }

    private void collectDeclaredOpsFromProgram(
            final List<Pair<? extends Operator, Boolean>> declaredOps) {
        final JavaASTFindPathWalker<Pair<? extends Operator, Boolean>> declaredSymbolsWalker = //
                new JavaASTFindPathWalker<>(block,
                        pe -> pe instanceof VariableDeclaration
                                || pe instanceof AbstractPlaceholderStatement,
                        this::extractDeclaredOpsFromPE);
        declaredOps.addAll(declaredSymbolsWalker.walk(method.getBody()));
    }

    private void addDeclaredDefaults(
            final List<Pair<? extends Operator, Boolean>> declaredOps) {
        final List<de.uka.ilkd.key.logic.op.Operator> declaredDefaults = new ArrayList<>();
        declaredDefaults.add(heap());
        declaredDefaults.add(typeConverter.getLocSetLDT().getAllLocs());
        declaredDefaults.add(typeConverter.getLocSetLDT().getEmpty());

        declaredDefaults.stream().map(op -> new Pair<>(op, false))
                .forEach(p -> declaredOps.add(p));
    }

    private void collectDeclaredSkolemLocSetsFromMethodContract(
            final List<Pair<? extends Operator, Boolean>> declaredOps) {
        /*
         * TODO (DS, 2019-01-14): Check whether there can be multiple contracts
         * with that particular base name. In this case, we might have to filter
         * for the one that has a declares directive
         */
        final Optional<FunctionalOperationContract> maybeMethodContract = services
                .getSpecificationRepository()
                .getOperationContracts(method.getContainerType(), method)
                .stream().filter(contr -> contr.getBaseName()
                        .equals("JML operation contract"))
                .findFirst();
        maybeMethodContract.map(FunctionalOperationContract::getDeclares)
                .map(this::extractDeclaredSkolemLocSetConsts)
                .ifPresent(declaredOps::addAll);
    }

    private void collectParameters(
            final List<Pair<? extends Operator, Boolean>> declaredOps) {
        declaredOps.addAll(method.getParameters().stream()
                .map(decl -> new Pair<>(
                        decl.getVariables().get(0).getProgramVariable(),
                        decl.isFinal()))
                .collect(Collectors.toList()));
    }

    private void collectFields(
            final List<Pair<? extends Operator, Boolean>> declaredOps) {
        final Type containerType = method.getContainerType().getJavaType();
        if (containerType instanceof ClassDeclaration) {
            final ClassDeclaration classDecl = (ClassDeclaration) containerType;
            declaredOps.addAll(classDecl.getAllFields(null).stream()
                    .filter(FieldSpecification.class::isInstance)
                    .map(FieldSpecification.class::cast)
                    .map(FieldSpecification::getProgramVariable)
                    .map(LocationVariable.class::cast)
                    .map(lv -> new Pair<>(
                            services.getTypeConverter().getHeapLDT()
                                    .getFieldSymbolForPV(lv, services),
                            lv.isFinal()))
                    .collect(Collectors.toList()));
        }
    }

    private List<Pair<? extends Operator, Boolean>> extractDeclaredOpsFromPE(
            ProgramElement pe) {
        if (pe instanceof VariableDeclaration) {
            return getTargetsFromVarDecl((VariableDeclaration) pe);
        } else if (pe instanceof AbstractPlaceholderStatement) {
            return getDeclsFromAbstrPlaceholderStmt(
                    (AbstractPlaceholderStatement) pe);
        } else {
            // impossible since not called then...
            throw new RuntimeException();
        }
    }

    private List<Pair<? extends Operator, Boolean>> getDeclsFromAbstrPlaceholderStmt(
            AbstractPlaceholderStatement aps) {
        final List<BlockContract> contracts = //
                AbstractExecutionUtils.getNoBehaviorContracts(aps, services);

        /* At this point, there should at most be one contract... */

        assert contracts.size() <= 1;

        if (contracts.isEmpty()) {
            return Collections.emptyList();
        }

        final BlockContract contract = contracts.iterator().next();

        final Term declaresTerm = contract.getDeclares(heap());

        return extractDeclaredSkolemLocSetConsts(declaresTerm);
    }

    private List<Pair<? extends Operator, Boolean>> extractDeclaredSkolemLocSetConsts(
            final Term declaresTerm) {
        /*
         * The declares term is a (possibly singleton) union of
         *
         * @formatter:off
         * - allLocs
         * - empty -- this is ignored, it's a default. We return the empty list
         *            for this constant.
         * - LocSet constants -- they are added to the result as non-final declared LocSets.
         * - final(locset) terms, where lofset is a LocSet constant -- for those, locset
         *     is added as a final declared LocSet.
         * @formatter:on
         */

        final DeclaredLocSetsVisitor declLSVisitor = //
                new DeclaredLocSetsVisitor(typeConverter.getLocSetLDT());
        /*
         * NOTE (DS, 2019-01-14): Have to walk in preorder to handle the final
         * specifier correctly.
         */
        declaresTerm.execPreOrder(declLSVisitor);

        return declLSVisitor.getResult();
    }

    private List<Pair<? extends Operator, Boolean>> getTargetsFromVarDecl(
            VariableDeclaration decl) {
        return decl.getVariables().stream()
                .map(VariableSpecification::getProgramVariable)
                .map(pv -> new Pair<>(pv, decl.isFinal()))
                .collect(Collectors.toList());
    }

    /**
     * Returns the target operators in a set-like union term. Expects a union
     * term consisting of (1) Skolem loc set functions (result will contain that
     * function), (2) singletonPV(...) applications on location variables
     * (result will contain the variable), and (3) singleton(...) applications
     * on an object and a function symbol representing a field (result will
     * contain the function symbol).
     *
     * @param t
     *            The loc set union term to dissect.
     * @param t
     *            The union function symbol, for instance of the LocSet theory.
     * @param services
     *            The {@link Services} object (for {@link TypeConverter}.
     * @return The {@link Operator}s in the {@link Term} (location variables,
     *         field function symbols, and Skolem location set functions).
     */
    private static Set<Operator> collectElementsOfLocSetTerm(Term t,
            de.uka.ilkd.key.logic.op.Function union, Services services) {
        return MiscTools.disasembleSetTerm(t, union).stream()
                .map(AbstractExecutionUtils.locSetElemTermsToOpMapper(services))
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
    }

    private static class JavaASTFindPathWalker<C> {
        private final ProgramElement searched;
        private final Predicate<ProgramElement> filter;
        private final Function<ProgramElement, ? extends Collection<C>> mapper;

        private boolean elemFound = false;

        public JavaASTFindPathWalker(ProgramElement searched,
                Predicate<ProgramElement> filter,
                Function<ProgramElement, ? extends Collection<C>> mapper) {
            this.searched = searched;
            this.filter = filter;
            this.mapper = mapper;
        }

        public List<C> walk(ProgramElement node) {
            final List<C> result = new ArrayList<>();

            if (filter.test(node)) {
                result.addAll(mapper.apply(node));
            }

            if (node instanceof NonTerminalProgramElement) {
                // increase depth
                NonTerminalProgramElement nonTerminalNode = (NonTerminalProgramElement) node;
                for (int i = 0; i < nonTerminalNode.getChildCount(); i++) {
                    final ProgramElement child = nonTerminalNode.getChildAt(i);

                    if (child == searched) {
                        elemFound = true;
                        return result;
                    }

                    if (child != null) {
                        final List<C> childResult = walk(child);
                        result.addAll(childResult);
                    }
                }

                // decrease depth
                /*
                 * At this point, we exit a container statement in which we did
                 * not find the searched element -> clear current result list!
                 */
                if (node instanceof StatementContainer && !elemFound
                        && !(((StatementContainer) node).getChildCount() == 1
                                && ((StatementContainer) node).getChildAt(
                                        0) instanceof AbstractPlaceholderStatement)) {
                    return Collections.emptyList();
                }
            }

            return result;
        }
    }

    private static class DeclaredLocSetsVisitor extends DefaultVisitor {
        private final LocSetLDT locSetLDT;
        private final List<Pair<? extends Operator, Boolean>> result = new ArrayList<>();
        private static final Consumer<? super Pair<? extends Operator, Boolean>> EMPTY_CONSUMER = //
                op -> {
                    return;
                };

        public DeclaredLocSetsVisitor(LocSetLDT locSetLDT) {
            this.locSetLDT = locSetLDT;
        }

        @Override
        public void visit(Term visited) {
            if (visited.op() == locSetLDT.getFinal()) {
                /* a "final(locSet)" term -- add the argument as final. */
                assert visited.subs().size() == 1
                        && visited.sub(0).subs().size() == 0;
                result.add(new Pair<>(visited.sub(0).op(), true));
            } else if (visited.subs().size() == 0
                    && visited.op() != locSetLDT.getEmpty()) {
                /*
                 * a LocSet constant -- add as non-final if not seen before
                 * (because then, it's most likely already added as a final
                 * LocSet, or it's redundant).
                 */
                result.stream().filter(pair -> pair.first == visited.op())
                        .findAny().ifPresentOrElse(EMPTY_CONSUMER, //
                                () -> result
                                        .add(new Pair<>(visited.op(), false)));
            }
        }

        public List<Pair<? extends Operator, Boolean>> getResult() {
            return result;
        }
    }
}
