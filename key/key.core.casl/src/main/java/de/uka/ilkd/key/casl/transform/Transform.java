package de.uka.ilkd.key.casl.transform;

import de.uka.ilkd.key.casl.parser.*;

import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uka.ilkd.key.casl.parser.CaslVisitor.*;

public final class Transform {

    private final Set<String> sorts = new HashSet<>();
    private final Map<String, Function> functions = new HashMap<String,Function>();
    private String problem;

    public Taclet transform(Specification spec) {
        List<Sort> sorts = collectSorts(spec);
        List<Function> funcs = collectFunctions(spec);
        Map<String, Function> defaultValues = collectDefaultValues(spec, funcs);
        List<Axiom> axioms = collectAxioms(spec);
        List<Rule> rules = collectRules(spec);
        List<Induction> inductionRules = collectInductions(spec);
        List<Split> splitRules = collectSplits(spec);

//        List<Equality> equalities = generateEqualityAxioms(axioms, spec);
        List<Equality> equalities = Collections.emptyList();

        List<Axiom> eqAxioms = collectEqAxioms(spec);
        eqAxioms.stream().forEach(axioms::add);

        return new Taclet(sorts, defaultValues, funcs, axioms, rules, inductionRules, splitRules, equalities, problem);
    }

    List<Axiom> collectEqAxioms(Specification spec) {
        List<Axiom> eqs = new LinkedList<>();
        for (var op : spec.operations()) {
            if (op.equality().eq()) {
                String opName = op.opName();
                OpType type = op.type();
                Sort ret = new Sort(type.sortRet().name());
                List<CaslVisitor.Sort> args = type.sortArgs();

                if (!"boolean".equals(ret.name)) {
                    throw new IllegalArgumentException("equality annotated functions require boolean return value");
                }

                if (args.size() != 2) {
                    throw new IllegalArgumentException("equality annotated functions require two arguments");
                }

                if (!args.get(0).name().equals(args.get(1).name())) {
                    throw new IllegalArgumentException("equality annotated functions require two arguments of same sort");
                }

                Sort sort = new Sort(args.get(0).name());
                String a1 = String.format("%s1", sort.name().substring(0,1).toLowerCase());
                String a2 = String.format("%s2", sort.name().substring(0,1).toLowerCase());
                List<SchemaVar> schemaVars = List.of(new SchemaVar(SchemaVarType.term, a1, sort),
                        new SchemaVar(SchemaVarType.term, a2, sort));

                String name = String.format("eq_%s_%s_%s", sort.name, a1, a2);
                DataTypeHeuristic heuristic = op.equality().heuristic();
                Axiom eq = new Axiom(name, schemaVars, new EqExpression(new Id(a1), new Id(a2)),
                        new FuncCall(opName, List.of(new Id(a1), new Id(a2))),
                        heuristic != null ? heuristic.heuristic() : null);
                eqs.add(eq);
            }
        }
        return eqs;
    }

    List<Equality> generateEqualityAxioms(List<Axiom> axioms, Specification spec) {
        return spec.dataTypes().stream()
                .filter(dt -> !dt.flags().contains(DataTypeFlag.FREE))
                .flatMap(Transform::toEquality)
                .toList();
    }

    private static Stream<Equality> toEquality(DataType dataType) {
        Sort sort = new Sort(dataType.sort().name());
        List<Equality> eqls = new LinkedList<>();
        for (Alternative alt : dataType.alternatives()) {
            String opName = alt.opName();
            int varNum = 0;
            List<SchemaVar> schemaVars = new LinkedList<>();
            for (Component comp : alt.components()) {
                if (comp instanceof OpComponent op) {
                    List<String> compNames = op.opNames();
                    Sort compSort = new Sort(op.sort().name());
                    String varName = String.format("var_%d", varNum++);
                    schemaVars.add(new SchemaVar(SchemaVarType.variable, varName, compSort));
                }
            }
            String eqlName = String.format("eql_%s_%s", sort.name(), opName);
            eqls.add(new Equality(eqlName, sort, opName, schemaVars));
        }
        return eqls.stream();
    }

    private List<Split> collectSplits(Specification spec) {
        return spec.dataTypes().stream().map(this::createOneSplit).flatMap(Optional::stream).toList();
    }

    public Transform problem(String problem) {
        this.problem = Objects.requireNonNull(problem);
        return this;
    }

    public record Split(String name, SchemaVar base, Map<String, List<SchemaVar>> alts) {
        public boolean getNumVarConds() {
            return alts.values().stream().flatMap(List::stream).count() > 0;
        }

        public List<SchemaVar> getAllSchemaVars() {
            List<SchemaVar> schemaVars = alts.entrySet().stream()
                    .flatMap(e -> e.getValue().stream())
                    .sorted(Comparator.comparing(v -> v.name))
                    .distinct()
                    .toList();
            return schemaVars;
        }
    }

    private Optional<Split> createOneSplit(DataType dataType) {
        if (!dataType.flags().contains(DataTypeFlag.GENERATED) && !dataType.flags().contains(DataTypeFlag.FREE))
            return Optional.empty();

        String splitName = String.format("%s_ctor_split", dataType.sort().name().toLowerCase());
        Sort sort = new Sort(dataType.sort().name());
        SchemaVar base = new SchemaVar(SchemaVarType.term, dataType.sort().name().toLowerCase(), sort);

        Map<String,List<SchemaVar>> alternatives = new LinkedHashMap<>();

        for (var alt : dataType.alternatives()) {
            String opName = alt.opName(); // can be something like nil in list context
            Set<SchemaVar> schemaVars = new HashSet<>();
            for (var comp : alt.components()) {
                if (comp instanceof OpComponent op) {
                    Sort s = new Sort(op.sort().name());
                    for (String o : op.opNames()) {
                        schemaVars.add(new SchemaVar(SchemaVarType.skolemTerm, o, s));
                    }
                } else if (comp instanceof SortComponent sortComp) {
                    Sort s = new Sort(sortComp.sort().name());
                    schemaVars.add(new SchemaVar(SchemaVarType.skolemTerm, "arg", s));
                } else {
                    throw new IllegalArgumentException();
                }
            }
            alternatives.put(opName, schemaVars.stream().sorted(Comparator.comparing(SchemaVar::name)).toList());
        }

        if (alternatives.size() >= 2) {
            return Optional.of(new Split(splitName, base, alternatives));
        } else {
            return Optional.empty();
        }
    }

    public record InductionCase(String name, List<SchemaVar> schemaVars, List<SchemaVar> inductionVar) {
        public boolean getRecursive() {
            return !inductionVar.isEmpty();
        }

        public boolean getBase() {
            return inductionVar.size() == 1;
        }
    }

    public record Induction(String name, Sort sort, SchemaVar base, Collection<SchemaVar> schemaVars, List<InductionCase> cases) {}

    private static long countSortsInVars(List<SchemaVar> vars, Sort sort) {
        return vars.stream().filter(v -> v.sort().equals(sort)).count();
    }

    private Optional<Induction> createOneInduction(DataType dt) {
        if (!dt.flags().contains(DataTypeFlag.GENERATED) && !dt.flags().contains(DataTypeFlag.FREE))
            return Optional.empty();

        final String inductionName = String.format("%s_induction", dt.sort().name().toLowerCase());
        final Sort sort = new Sort(dt.sort().name());
        final SchemaVar base = new SchemaVar(SchemaVarType.variable, "base", sort);
        final List<InductionCase> cases = new LinkedList<>();
        for (var alt : dt.alternatives()) {
            final List<SchemaVar> schemaVars = new LinkedList<>();
            for (var op : alt.components()) {
                if (op instanceof OpComponent opc) {
                    Sort argSort = new Sort(opc.sort().name());
                    for (String s : opc.opNames()) {
                        schemaVars.add(new SchemaVar(SchemaVarType.variable, s, argSort));
                    }
                }
            }

            var indVars = schemaVars.stream().filter(v -> v.sort.equals(sort)).toList();
            if (indVars.size() == 1) {
                var vid = indVars.get(0);
                schemaVars.replaceAll(v -> v == vid ? base : v);
                indVars = Collections.singletonList(base);
                }
            cases.add(new InductionCase(alt.opName(), Collections.unmodifiableList(schemaVars), indVars));
        }

        Collection<SchemaVar> schemaVars = cases.stream()
                .map(InductionCase::schemaVars)
                .flatMap(List::stream)
                .filter(var -> var != base)
                .collect(Collectors.toMap(SchemaVar::name, java.util.function.Function.identity()))
                .values();

        Collections.sort(cases, Comparator.comparingLong(c -> countSortsInVars(c.schemaVars(), sort)));

        if (cases.size() > 1) {
            return Optional.of(new Induction(inductionName, new Sort(dt.sort().name()), base, schemaVars, Collections.unmodifiableList(cases)));
        } else {
            return Optional.empty();
        }
    }

    private List<Induction> collectInductions(Specification spec) {
        return spec.dataTypes().stream().map(this::createOneInduction).flatMap(Optional::stream).toList();
    }

    private List<Axiom> collectAxioms(Specification spec) {
        List<FormulaEnv> formula = spec.formula();
        List<Axiom> axioms = formula.stream()
                .map(this::collectOneAxiom)
                .filter(Optional::isPresent)
                .map(Optional::get)
                .collect(Collectors.toList());
        return axioms;
    }

    private Optional<Axiom> collectOneAxiom(FormulaEnv formula) {
        Formula form = formula.f();
        String heuristic = formula.heuristic() != null ? formula.heuristic().heuristic() : null;
            List<Var> vars = formula.vars();
            List<SchemaVar> schemaVars = vars.stream().map(v ->
                    new SchemaVar(SchemaVarType.term, v.name().toLowerCase(), new Sort(v.sort().name()))).toList();
        String name = form.tacletName();
        if (form instanceof EqTerm t) {
            return Optional.of(new Axiom(name, schemaVars, transformTerms(t.t1()),
                    transformTerms(t.t2()), heuristic));
        } else if (form instanceof EqFormula eqFormula) {
            Formula f1 = eqFormula.f1();
            Formula f2 = eqFormula.f2();
            return Optional.of(new Axiom(name, schemaVars, transformFormula(f1), transformFormula(f2), heuristic));
        } else if (form instanceof ConjFormula conj) {
            Formula f1 = conj.f1();
            Formula f2 = conj.f2();
            return Optional.of(new Axiom(name, schemaVars, transformFormula(f1), transformFormula(f2), heuristic));
        } else if (form instanceof DisjFormula disj) {
            Formula f1 = disj.f1();
            Formula f2 = disj.f2();
            return Optional.of(new Axiom(name, schemaVars, transformFormula(f1), transformFormula(f2), heuristic));
        } else {
            return Optional.empty();
        }
    }

    Expression transformFormula(Formula f) {
        Expression expr = switch (f) {
            case EqFormula eqf -> simplify(new EqExpression(transformFormula(eqf.f1()), transformFormula(eqf.f2())));
            case EqTerm eqt -> simplify(new EqExpression(transformTerms(eqt.t1()), transformTerms(eqt.t2())));
            case ConjFormula conj -> new ConjExpression(transformFormula(conj.f1()), transformFormula(conj.f2()));
            case DisjFormula disj -> new DisjExpression(transformFormula(disj.f1()), transformFormula(disj.f2()));
            default -> throw new IllegalArgumentException(String.format("%s not yet supported", f.getClass()));
        };
        return expr;
    }

    private Expression simplify(EqExpression eqExpression) {
        Expression left = eqExpression.left();
        Expression right = eqExpression.right();

        if (left instanceof Expressions exprs && exprs.exprs().size() == 1) {
            left = exprs.exprs().get(0);
        }

        if (right instanceof Expressions exprs && exprs.exprs().size() == 1) {
            right = exprs.exprs().get(0);
        }

        if (left instanceof Literal lit) {
            if (lit.name().equals("true")) {
                return right;
            }
        }

        if (right instanceof Literal lit) {
            if (lit.name().equals("true")) {
                return left;
            }
        }

        return eqExpression;
    }

    private Expression transformTerms(Terms terms) {
        return new Expressions(terms.terms().stream().map(t -> transformTerm(t)).toList(), terms.pars());
    }

    private Expression transformTerm(CaslVisitor.Term term) {
        return switch (term) {
            case FuncTerm ft -> new FuncCall(ft.name(), ft.args().stream().map(this::transformTerm).toList());
            case IdTerm id -> new Id(id.name());
            case LiteralTerm l -> new Literal(l.literal());
            case Terms ts -> transformTerms(ts);
        };
    }

    private List<Rule> collectRules(Specification spec) {
        return List.of();
    }

    private Map<String,Function> collectDefaultValues(Specification spec, List<Function> functions) {
        Map<String,Function> map = new HashMap<>();
        Map<String, Function> funcs = functions.stream().collect(
                Collectors.toMap(Function::name, java.util.function.Function.identity()));
        for (var dt : spec.dataTypes()) {
            String sort = dt.sort().name();
            Function dflValue = funcs.get(dt.defaultValue().defaultValue());
            map.put(sort, dflValue);
        }
        return Collections.unmodifiableMap(map);
    }

    private List<Sort> collectSorts(Specification spec) {
        Set<Sort> sorts = new HashSet<Sort>();
        spec.dataTypes().stream()
                .map(dt -> new Sort(dt.sort().name(), dt.extend().extend()))
                .forEach(sorts::add);
//        collectArgumentSorts(spec).forEach(sorts::add);
        return sorts.stream().sorted(Comparator.comparing(Sort::name)).toList();
    }

    private Stream<Sort> collectArgumentSorts(Specification spec) {
        return spec.dataTypes().stream()
                .flatMap(dt -> dt.alternatives().stream())
                .flatMap(a -> a.components().stream())
                .map(c -> switch (c) {
                    case OpComponent comp -> comp.sort().name();
                    case SortComponent sort -> sort.sort().name();
                })
                .map(Sort::new);
    }

    private Function oneFunc(CaslVisitor.OpItem func) {
        String name = func.opName();
        boolean unique = false;
        Sort retSort = new Sort(func.type().sortRet().name());
        List<Sort> args = func.type().sortArgs().stream().map(CaslVisitor.Sort::name).map(Sort::new).toList();
        return new Function(name, unique, retSort, args);
    }
    
    private List<Function> collectFunctions(Specification spec) {
        List<Function> funcs = new LinkedList<>();
        for (var dt : spec.dataTypes()) {
            boolean unique = dt.flags().contains(DataTypeFlag.FREE);
            Sort retValue = new Sort(dt.sort().name());
            dt.alternatives().stream()
                    .map(alt -> new Function(alt.opName(), unique, retValue, collectArgs(alt)))
                    .forEach(funcs::add);
        }
        spec.operations().stream().map(this::oneFunc).forEach(funcs::add);
        return Collections.unmodifiableList(funcs);
    }

    private List<Sort> collectArgs(Alternative alt) {
        return alt.components().stream().map(c -> switch (c) {
            case OpComponent opc -> opc.sort().name();
            case SortComponent sc -> sc.sort().name();
        }).map(Sort::new).toList();
    }

    public record Taclet(List<Sort> sorts,
                         Map<String,Function> defaultValues,
                         List<Function> functions,
                         List<Axiom> axioms,
                         List<Rule> rules,
                         List<Induction> induction,
                         List<Split> split,
                         List<Equality> equalities,
                         String problem) {}

    public record Sort(String name, String extend) {
        Sort(String name) {
            this(name, null);
        }
    }

    public record Function(String name, boolean unique, Sort retSort, List<Sort> args) {}

    enum SchemaVarType {
        formula,
        variable,
        term,
        skolemTerm
        ;

        public String getTacletString() {
            return this.toString();
        }
    }

    public record SchemaVar(SchemaVarType schemaType, String name, Sort sort) {}

    sealed interface Expression permits FuncCall, Id, Literal, EqExpression, DisjExpression, ConjExpression, Expressions {
        default String getSeparator() {
            throw new IllegalStateException();
        }
    }
    public record FuncCall(String name, List<Expression> args) implements Expression {}
    public record Id(String name) implements Expression {}
    public record Literal(String name) implements Expression {}
    public record EqExpression(Expression left, Expression right) implements Expression {
        @Override
        public String getSeparator() {
            return "=";
        }
    }
    public record DisjExpression(Expression left, Expression right) implements Expression {
        @Override
        public String getSeparator() {
            return "|";
        }
    }
    public record ConjExpression(Expression left, Expression right) implements Expression {
        @Override
        public String getSeparator() {
            return "&";
        }
    }
    public record Expressions(List<Expression> exprs, boolean par) implements Expression {
        public String getSeparator() { return ""; }
    }

    public record Equality(String name, Sort sort, String opName, List<SchemaVar> schemaVars) {}

    public record Axiom(String name, List<SchemaVar> schemaVars, Expression focus, Expression replacement,
                        String heuristic) {}

    public record Rule() {}
}
