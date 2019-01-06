package de.uka.ilkd.key.speclang.jml.translation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.declaration.VariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory.ContractClauses;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
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
 * TODO (DS, 2019-01-04): We currently have no directive for specifying the
 * declaration of Skolem loc sets, therefore we just check whether they are
 * specified as assignable before. This can lead to situations of program that
 * type-check although they shouldn't, e.g. if a program Q assigns the locals of
 * a program P which is not in scope.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractPlaceholderSpecsTypeChecker {
    private final IProgramMethod method;
    private final StatementBlock block;
    private final Services services;
    private final ContractClauses clauses;
    private final AbstractPlaceholderStatement aps;

    public AbstractPlaceholderSpecsTypeChecker(IProgramMethod method,
            StatementBlock block, ContractClauses clauses, Services services) {
        assert block.getChildAt(0) instanceof AbstractPlaceholderStatement;

        this.method = method;
        this.aps = (AbstractPlaceholderStatement) block.getChildAt(0);
        this.block = block;
        this.clauses = clauses;
        this.services = services;
    }

    public void check() throws SLTranslationException {
        final TypeConverter typeConverter = services.getTypeConverter();

        final List<Pair<? extends Operator, Boolean>> declaredOps = //
                getDeclaredOps(typeConverter);

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

            if (collectOps(assignablesTerm()).contains(heap())) {
                throw new SLTranslationException(String.format(
                        "Abstract program %s is specified to assign the heap, "
                                + "but containing method %s is declared static.",
                        aps.getId(), method.name()));
            }

            if (collectOps(accessiblesTerm()).contains(heap())) {
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
        final TypeConverter typeConverter = services.getTypeConverter();
        return typeConverter.getHeapLDT().getHeap();
    }

    private List<Operator> getUndeclaredAccessedOps(
            List<Pair<? extends Operator, Boolean>> declaredOps) {
        final Set<Operator> collectedOps = collectOps(accessiblesTerm());
        return collectedOps.stream().filter(op -> op.arity() == 0).filter(
                op -> !declaredOps.stream().anyMatch(p -> p.first.equals(op)))
                .collect(Collectors.toList());
    }

    private List<Operator> getAssignedFinalOps(
            List<Pair<? extends Operator, Boolean>> declaredOps) {
        final Set<Operator> collectedOps = collectOps(assignablesTerm());
        return collectedOps.stream().filter(op -> op.arity() == 0)
                .filter(op -> declaredOps.stream()
                        .anyMatch(p -> p.first.equals(op) && p.second))
                .collect(Collectors.toList());
    }

    private static Set<Operator> collectOps(Term t) {
        final OpCollector opColl = new OpCollector();
        t.execPostOrder(opColl);
        final Set<Operator> collectedOps = opColl.ops();
        return collectedOps;
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

    private List<Pair<? extends Operator, Boolean>> getDeclaredOps(
            final TypeConverter typeConverter) {
        final List<Pair<? extends Operator, Boolean>> declaredOps = new ArrayList<>();
        final JavaASTFindPathWalker<Pair<? extends Operator, Boolean>> declaredSymbolsWalker = //
                new JavaASTFindPathWalker<>(block,
                        pe -> pe instanceof VariableDeclaration
                                || pe instanceof AbstractPlaceholderStatement,
                        this::extractOpsFromPE);

        declaredOps.addAll(declaredSymbolsWalker.walk(method.getBody()));
        declaredOps.addAll(extractDeclaredSkolemLocSetConsts(typeConverter,
                declaresTerm()));
        declaredOps.addAll(method.getParameters().stream()
                .map(decl -> new Pair<>(
                        decl.getVariables().get(0).getProgramVariable(),
                        decl.isFinal()))
                .collect(Collectors.toList()));

        final List<de.uka.ilkd.key.logic.op.Operator> declaredDefaults = new ArrayList<>();
        declaredDefaults.add(heap());
        declaredDefaults.add(typeConverter.getLocSetLDT().getAllLocs());
        declaredDefaults.add(typeConverter.getLocSetLDT().getEmpty());

        declaredDefaults.stream().map(op -> new Pair<>(op, false))
                .forEach(p -> declaredOps.add(p));

        return declaredOps;
    }

    private List<Pair<? extends Operator, Boolean>> extractOpsFromPE(
            ProgramElement pe) {
        if (pe instanceof VariableDeclaration) {
            return getTargetsFromVarDecl((VariableDeclaration) pe);
        }
        else if (pe instanceof AbstractPlaceholderStatement) {
            return getDeclsFromAbstrPlaceholderStmt(
                    (AbstractPlaceholderStatement) pe);
        }
        else {
            // impossible since not called then...
            throw new RuntimeException();
        }
    }

    private List<Pair<? extends Operator, Boolean>> getDeclsFromAbstrPlaceholderStmt(
            AbstractPlaceholderStatement aps) {
        final TypeConverter typeConverter = services.getTypeConverter();
        final List<BlockContract> contracts = services
                .getSpecificationRepository()
                .getAbstractPlaceholderStatementContracts(aps).stream()
                .filter(contract -> contract.getBaseName()
                        .equals("JML block contract"))
                /*
                 * We exclude return_behavior etc. here, because from those
                 * contracts we only consider the precondition.
                 */
                .collect(Collectors.toList());

        /* At this point, there should at most be one contract... */

        assert contracts.size() <= 1;

        if (contracts.isEmpty()) {
            return Collections.emptyList();
        }

        final BlockContract contract = contracts.iterator().next();

        final Term declaresTerm = contract.getDeclares(heap());

        return extractDeclaredSkolemLocSetConsts(typeConverter, declaresTerm);
    }

    private List<Pair<? extends Operator, Boolean>> extractDeclaredSkolemLocSetConsts(
            final TypeConverter typeConverter, final Term declaresTerm) {
        final OpCollector opColl = new OpCollector();
        declaresTerm.execPostOrder(opColl);

        /*
         * We only collect constants of LocSet type like localsP for the local
         * variables of abstract program P etc.
         */
        return opColl.ops().stream().filter(op -> {
            return op instanceof de.uka.ilkd.key.logic.op.Function
                    && ((de.uka.ilkd.key.logic.op.Function) op)
                            .sort() == typeConverter.getLocSetLDT().targetSort()
                    && op.arity() == 0;
        }).map(op -> new Pair<>(op, false)).collect(Collectors.toList());
    }

    private List<Pair<? extends Operator, Boolean>> getTargetsFromVarDecl(
            VariableDeclaration decl) {
        return decl.getVariables().stream()
                .map(VariableSpecification::getProgramVariable)
                .map(pv -> new Pair<>(pv, decl.isFinal()))
                .collect(Collectors.toList());
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
}
