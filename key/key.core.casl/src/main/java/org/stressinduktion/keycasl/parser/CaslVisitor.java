package org.stressinduktion.keycasl.parser;

import org.antlr.v4.runtime.BufferedTokenStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import javax.xml.crypto.Data;
import java.util.Collections;
import java.util.EnumSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Objects;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public final class CaslVisitor extends CASLParserBaseVisitor<Object> {
    private final ArgumentManager arguments = new ArgumentManager();
    private final BufferedTokenStream tokens;

    public CaslVisitor(TokenStream tokens) {
        this.tokens = (BufferedTokenStream) tokens;
    }


    private <T> T $(ParseTree ctx) {
        arguments.pushScope();
        try {
            return (T) visit(ctx);
        } finally {
            arguments.popScope();
        }
    }

    private <T> void putArg(Class<T> clazz, T obj) {
        arguments.putArg(clazz, obj);
    }

    private <T> T getArg(Class<T> clazz) {
        return (T) arguments.getArg(clazz);
    }

    private <T> void forwardOneArg(Class<T> clazz) {
        T obj = Objects.requireNonNull(getArg(clazz));
        putArg(clazz, obj);
    }

    private void forwardArgs(Class<?>... clazzes) {
        for (var clz : clazzes) {
            forwardOneArg(clz);
        }
    }

    /* parser */

    @Override
    public IdTerm visitTermId(CASLParser.TermIdContext ctx) {
        return new IdTerm(ctx.id().getText());
    }

    @Override
    public FuncTerm visitTermFunc(CASLParser.TermFuncContext ctx) {
        List<Term> args = ctx.terms().term().stream().map(t -> (Term) $(t)).toList();
        return new FuncTerm(ctx.id().getText(), args);
    }

    @Override
    public Object visitTermLiteral(CASLParser.TermLiteralContext ctx) {
        String text = stripQuotes(ctx.getText());
        return new LiteralTerm(text);
    }

    private static String stripQuotes(String text) {
        if (text.startsWith("\"") && text.endsWith("\"")) {
            text = text.substring(1, text.length() - 1);
        }
        return text;
    }

    @Override
    public Object visitFormulaEqTerm(CASLParser.FormulaEqTermContext ctx) {
        return new EqTerm($(ctx.term(0)), $(ctx.term(1)));
    }

    @Override
    public NotFormula visitFormulaNot(CASLParser.FormulaNotContext ctx) {
        return new NotFormula($(ctx.formula()));
    }

    @Override
    public ConjFormula visitFormulaConj(CASLParser.FormulaConjContext ctx) {
        return new ConjFormula($(ctx.formula(0)), $(ctx.formula(1)));
    }

    @Override
    public ImplFormula visitFormulaImpl(CASLParser.FormulaImplContext ctx) {
        return new ImplFormula($(ctx.formula(0)), $(ctx.formula(1)));
    }

    @Override
    public IfFormula visitFormulaIf(CASLParser.FormulaIfContext ctx) {
        return new IfFormula($(ctx.formula(0)), $(ctx.formula(1)));
    }

    @Override
    public Object visitFormulaEq(CASLParser.FormulaEqContext ctx) {
        return new EqFormula($(ctx.formula(0)), $(ctx.formula(1)));
    }

    @Override
    public Quantifier visitQuantifier(CASLParser.QuantifierContext ctx) {
        if (ctx.FORALL() != null) {
            return new Forall();
        }
        if (ctx.EXISTS() != null) {
            return new Exists();
        }
        if (ctx.EXISTSB() != null) {
            return new ExistsBang();
        }
        return null;
    }

    @Override
    public List<Var> visitVar_decl(CASLParser.Var_declContext ctx) {
        List<Var> vars = new LinkedList<>();
        Sort sort = $(ctx.sort());
        for (var v : ctx.var()) {
            vars.add(new Var(v.getText(), sort));
        }
        return Collections.unmodifiableList(vars);
    }

    @Override
    public QFormula visitFormulaQ(CASLParser.FormulaQContext ctx) {
        Quantifier q = $(ctx.quantifier());
        Formula f = $(ctx.formula());
        List<Var> vars = new LinkedList<>();
        for (var v : ctx.var_decl()) {
            vars.addAll($(v));
        }
        return new QFormula(q, vars, f);
    }

    @Override
    public DisjFormula visitFormulaDisj(CASLParser.FormulaDisjContext ctx) {
        return new DisjFormula($(ctx.formula().get(0)), $(ctx.formula().get(1)));
    }

    @Override
    public TrueFormula visitFormulaTrue(CASLParser.FormulaTrueContext ctx) {
        return new TrueFormula();
    }

    @Override
    public FalseFormula visitFormulaFalse(CASLParser.FormulaFalseContext ctx) {
        return new FalseFormula();
    }

    @Override
    public Void visitBasicItemForallFormula(CASLParser.BasicItemForallFormulaContext ctx) {
        Specification spec = getArg(Specification.class);
        DataTypeHeuristic heuristic = keyAnnotationHeuristic(ctx);
        List<Var> vars = new LinkedList<>();
        for (var varDecl : ctx.var_decl()) {
            vars.addAll($(varDecl));
        }
        vars = Collections.unmodifiableList(vars);
//        for (var formula : ctx.formula()) {
            spec.addFormula($(ctx.formula()), vars, heuristic);
//        }
        return null;
    }

    @Override
    public Void visitBasicItemFormula(CASLParser.BasicItemFormulaContext ctx) {
        Specification spec = getArg(Specification.class);
        DataTypeHeuristic heuristic = keyAnnotationHeuristic(ctx);
        for (var f : ctx.formula()) {
            spec.addFormula($(f), List.of(), heuristic);
        }
        return null;
    }

    @Override
    public Formula visitFormulaP(CASLParser.FormulaPContext ctx) {
        return $(ctx.formula());
    }

    @Override
    public OpType visitOp_type(CASLParser.Op_typeContext ctx) {
        boolean partial = ctx.QUESTIONP() != null;
        List<Sort> sorts = ctx.args.stream().map(s -> (Sort) $(s)).toList();
        return new OpType($(ctx.retSort), sorts, partial);
    }

    @Override
    public Stream<OpItem> visitOp_item(CASLParser.Op_itemContext ctx) {
        DataTypeHeuristic dataTypeHeuristic = keyAnnotationHeuristic(ctx);
        OpEquality opEquality = keyAnnotationEquality(ctx);
        List<String> opNames = ctx.op_name().stream().map(n -> (String) $(n)).toList();
        OpType type = $(ctx.op_type());
        return opNames.stream().map(n -> new OpItem(n, type, opEquality));
    }

    @Override
    public Void visitSigItemOp(CASLParser.SigItemOpContext ctx) {
        Specification arg = getArg(Specification.class);
        List<OpItem> ops = ctx.op_item().stream().flatMap(op -> (Stream<OpItem>) $(op)).toList();
        arg.addOps(ops);
        return null;
    }


    @Override
    public String visitOp_name(CASLParser.Op_nameContext ctx) {
        return ctx.getText();
    }

    @Override
    public Component visitComponent(CASLParser.ComponentContext ctx) {
        if (ctx.op_name() != null) {
            List<String> opNames = ctx.op_name().stream().map(op -> (String) $(op)).toList();
            Sort sort = $(ctx.sort());
            boolean partial = ctx.QUESTIONP() != null || ctx.COLONQ() != null;
            return new OpComponent(opNames, sort, partial);
        } else {
            return new SortComponent($(ctx.sort()));
        }
    }

    @Override
    public Alternative visitAlternative(CASLParser.AlternativeContext ctx) {
        List<Component> comps = ctx.component().stream().map(c -> (Component) $(c)).toList();
        return new Alternative(ctx.op_name().getText(), comps);
    }

    @Override
    public Sort visitSortId(CASLParser.SortIdContext ctx) {
        return new Sort(ctx.WORDS().getText());
    }

    public DataType visitDatatype_decl(CASLParser.Datatype_declContext ctx) {
        DataTypeDefaultValue defaultVal = getArg(DataTypeDefaultValue.class);
        DataTypeExtends extend = getArg(DataTypeExtends.class);
        Sort sort = $(ctx.sort().sort_id());
        List<Alternative> alts = ctx.alternative().stream().map(a -> (Alternative) $(a)).toList();
        return new DataType(EnumSet.noneOf(DataTypeFlag.class), sort, alts, defaultVal, extend);
    }


    private static final Pattern RE_DEFAULT_VAL = Pattern.compile("%key\\(defaultValue=(.*)\\)%");
    private static final Pattern RE_EXTENDS = Pattern.compile("%key\\(extends=(.*)\\)%");
    private static final Pattern RE_HEURISTIC = Pattern.compile("%key\\(heuristic=(.*)\\)%");
    private static final Pattern RE_EQUALITY = Pattern.compile("%key\\(equality=(.*)\\)%");

    private List<Token> keyHiddenTokens(ParserRuleContext ctx) {
        Token end = ctx.getStop();
        int i = end.getTokenIndex();
        List<Token> hiddenTokensToRight = tokens.getHiddenTokensToRight(i, CASLLexer.C_KEY_ANNOTATION);
        return hiddenTokensToRight;
    }

    private String keyAnnotationValue(ParserRuleContext ctx, Pattern re) {
        List<Token> tokens = keyHiddenTokens(ctx);

        if (tokens == null)
            return null;

        for (var hToken : tokens) {
            String text = hToken.getText();
            Matcher matcher = re.matcher(text);
            if (matcher.find() && matcher.groupCount() == 1) {
                String group = matcher.group(1);
                return group;
            }
        }

        return null;
    }

    private DataTypeDefaultValue keyAnnotationDefaultValue(ParserRuleContext ctx) {
        String s = keyAnnotationValue(ctx, RE_DEFAULT_VAL);
        if (s == null) {
            return CaslError.error("no default value specified for datatype", ctx);
        } else {
            return new DataTypeDefaultValue(s);
        }
    }

    public record DataTypeExtends(String extend) {
        public static final DataTypeExtends EMPTY = new DataTypeExtends(null);
    }

    private DataTypeExtends keyAnnotationExtends(ParserRuleContext ctx) {
        String s = keyAnnotationValue(ctx, RE_EXTENDS);
        if (s == null) {
            return DataTypeExtends.EMPTY;
        } else {
            return new DataTypeExtends(s);
        }
    }

    public record DataTypeHeuristic(String heuristic) {}

    private DataTypeHeuristic keyAnnotationHeuristic(ParserRuleContext ctx) {
        String s = keyAnnotationValue(ctx, RE_HEURISTIC);
        if (s == null) {
            return null;
        } else {
            return new DataTypeHeuristic(s);
        }
    }

    public record OpEquality(boolean eq, DataTypeHeuristic heuristic) {
        public static OpEquality NO = new OpEquality(false, null);
    }

    private OpEquality keyAnnotationEquality(ParserRuleContext ctx) {
        String s = keyAnnotationValue(ctx, RE_EQUALITY);
        DataTypeHeuristic dataTypeHeuristic = keyAnnotationHeuristic(ctx);
        boolean b = Boolean.parseBoolean(s);
        return b ? new OpEquality(true, dataTypeHeuristic) : OpEquality.NO;
    }

    @Override
    public Void visitSigItemType(CASLParser.SigItemTypeContext ctx) {
        Specification spec = getArg(Specification.class);

        putArg(DataTypeDefaultValue.class, keyAnnotationDefaultValue(ctx));
        putArg(DataTypeExtends.class, keyAnnotationExtends(ctx));
        List<DataType> dataTypes = ctx.datatype_decl().stream().map(dt -> (DataType) $(dt)).toList();
        spec.addDataTypes(dataTypes);
        return null;
    }

    @Override
    public Void visitBasicItemDataTypeDecl(CASLParser.BasicItemDataTypeDeclContext ctx) {
        Specification spec = getArg(Specification.class);

        boolean free = ctx.FREE() != null;
        boolean generated = ctx.GENERATED() != null;
        putArg(DataTypeDefaultValue.class, keyAnnotationDefaultValue(ctx));
        putArg(DataTypeExtends.class, keyAnnotationExtends(ctx));
        List<DataType> datatypes = ctx.datatype_decl().stream().map(dt -> (DataType) $(dt)).toList();
        for (var d : datatypes) {
            if (free) {
                d.flags.add(DataTypeFlag.FREE);
            }
            if (generated) {
                d.flags.add(DataTypeFlag.GENERATED);
            }
        }


        spec.addDataTypes(datatypes);
        return null;
    }

    @Override
    public Void visitBasic_spec(CASLParser.Basic_specContext ctx) {
        for (var c : ctx.basic_items()) {
            $(c);
        }

        return null;
    }

    @Override
    public Void visitSpecBasicSpec(CASLParser.SpecBasicSpecContext ctx) {
        forwardArgs(Specification.class);
        for (var item : ctx.basic_spec().basic_items()) {
            $(item);
        }
        return null;
    }

    @Override
    public Specification visitSpecDefnPlain(CASLParser.SpecDefnPlainContext ctx) {
        String name = ctx.spec_name().getText();
        Specification spec = new Specification(name, new LinkedList<>(), new LinkedList<>(), new LinkedList<>());
        putArg(Specification.class, spec);
        $(ctx.spec());
        return spec;
    }

    @Override
    public Specification visitSpec_defn_eof(CASLParser.Spec_defn_eofContext ctx) {
        return $(ctx.spec_defn());
    }

    /* DATA MODEL */

    public record Library(String name, String version, List<Specification> specifications) {
        public void addSpecification(Specification spec) {
            specifications.add(spec);
        }
    }

    public record OpItem(String opName, OpType type, OpEquality equality) {
        public OpItem(String opName, OpType type) {
            this(opName, type, OpEquality.NO);
        }
    }

    public record OpType(Sort sortRet, List<Sort> sortArgs, boolean partial) {}

    public record Specification(String name, List<DataType> dataTypes,
                                List<OpItem> operations,
                                List<FormulaEnv> formula) {
        public void addDataTypes(List<DataType> dts) {
            dataTypes.addAll(dts);
        }

        public void addOps(List<OpItem> ops) {
            operations.addAll(ops);
        }

        public void addFormula(Formula f, List<Var> vars, DataTypeHeuristic heuristic) {
            formula.add(new FormulaEnv(f, vars, heuristic));
        }
    }

    public enum DataTypeFlag {
        FREE,
        GENERATED,
    }

    public record DataTypeDefaultValue(String defaultValue) {}
    public record DataType(EnumSet<DataTypeFlag> flags, Sort sort, List<Alternative> alternatives,
                           DataTypeDefaultValue defaultValue, DataTypeExtends extend) {}
    public record Sort(String name) {}

    public sealed interface Component permits OpComponent, SortComponent {}
    public record OpComponent(List<String> opNames, Sort sort, boolean partial) implements Component {}
    public record SortComponent(Sort sort) implements Component {}

    public record Alternative(String opName, List<Component> components) {}

    public sealed interface Quantifier permits Forall, Exists, ExistsBang {}
    public record Forall() implements Quantifier {}
    public record Exists() implements Quantifier {}
    public record ExistsBang() implements Quantifier {}

    public record FormulaEnv(Formula f, List<Var> vars, DataTypeHeuristic heuristic) {}

    public sealed interface Formula permits NotFormula, ConjFormula, DisjFormula, ImplFormula, IfFormula, EqFormula,
            QFormula, TrueFormula, FalseFormula, DefTerm, ExistEqTerm, EqTerm {
        String tacletName();
    }
    public record NotFormula(Formula f) implements Formula {
        @Override
        public String tacletName() {
            return String.format("not_%s", f.tacletName());
        }
    }
    public record ConjFormula(Formula f1, Formula f2) implements Formula {
        @Override
        public String tacletName() {
            return String.format("%s_%s", f1.tacletName(), f2.tacletName());
        }
    }
    public record DisjFormula(Formula f1, Formula f2) implements Formula {
        @Override
        public String tacletName() {
            return String.format("%s_%s", f1.tacletName(), f2.tacletName());
        }
    }
    public record ImplFormula(Formula f1, Formula f2) implements Formula {
        @Override
        public String tacletName() {
            return String.format("%s_%s", f1.tacletName(), f2.tacletName());
        }
    }
    public record IfFormula(Formula f1, Formula f2) implements Formula {
        @Override
        public String tacletName() {
            return String.format("%s_%s", f1.tacletName(), f2.tacletName());
        }
    }
    public record EqFormula(Formula f1, Formula f2) implements Formula {
        @Override
        public String tacletName() {
            return String.format("%s_%s", f1.tacletName(), f2.tacletName());
        }
    }
    public record QFormula(Quantifier q, List<Var> vars, Formula f) implements Formula {
        @Override
        public String tacletName() {
            return f.tacletName();
        }
    }
    public record TrueFormula() implements Formula {
        @Override
        public String tacletName() {
            return String.format("true_%d", this.hashCode());
        }
    }
    public record FalseFormula() implements Formula {
        @Override
        public String tacletName() {
            return String.format("false_%d", this.hashCode());
        }
    }
    public record DefTerm(Term t) implements Formula {
        @Override
        public String tacletName() {
            return t.tacletName();
        }
    }
    public record ExistEqTerm(Term t1, Term t2) implements Formula {
        @Override
        public String tacletName() {
            return String.format("%s_%s", t1.tacletName(), t2.tacletName());
        }
    }
    public record EqTerm(Term t1, Term t2) implements Formula {
        @Override
        public String tacletName() {
            return t1.tacletName();
        }
    }

    public sealed interface Term permits FuncTerm, IdTerm, LiteralTerm {
        default String tacletName() {
            return String.format("taclet_%d", this.hashCode());
        }
    }

    public record FuncTerm(String name, List<Term> args) implements Term {
        @Override
        public String tacletName() {
            String argStr = args.stream().map(a -> a.tacletName()).collect(Collectors.joining("_"));
            return String.format("%s_%s", name, argStr);
        }
    }
    public record IdTerm(String name) implements Term {
        @Override
        public String tacletName() {
            return name;
        }
    }

    public record LiteralTerm(String literal) implements Term {
        @Override
        public String tacletName() {
            return String.format("\"%s\"", literal);
        }
    }

    public record Var(String name, Sort sort) {}
}
