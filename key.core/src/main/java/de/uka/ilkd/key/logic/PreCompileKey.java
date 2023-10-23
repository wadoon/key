package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.KeYParserBaseVisitor;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.nparser.builder.BuilderHelpers;
import de.uka.ilkd.key.nparser.builder.DeclarationBuilder;
import de.uka.ilkd.key.proof.init.JavaProfile;
import org.antlr.v4.runtime.RuleContext;

import javax.annotation.Nonnull;
import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CompletionException;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ForkJoinPool;
import java.util.stream.Collector;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (23.10.23)
 */
public class PreCompileKey {
    static final Path outputDir = Paths.get("key.core/build/generated-src/ldt/de/uka/ilkd/key/proof/rulesc/");
    static ForkJoinPool executor = ForkJoinPool.commonPool();

    public static void main(String[] args) throws IOException, ExecutionException, InterruptedException {
        Files.createDirectories(outputDir);
        var ruleDir = Paths.get("key.core/src/main/resources/de/uka/ilkd/key/proof/rules");
        var files = Files.walk(ruleDir)
                .filter(it -> it.toString().endsWith(".key"))
                .map(it -> parse(it).thenAccept(PreCompileKey::translate))
                .toList();
        for (CompletableFuture<Void> file : files) {
            file.get();
        }
    }

    private static CompletableFuture<KeyAst.File> parse(Path it) {
        return CompletableFuture.supplyAsync(() -> {
                    try {
                        return ParsingFacade.parseFile(it);
                    } catch (Exception e) {
                        System.out.println(it);
                        throw new CompletionException("Error in " + it, e);
                    }
                }, executor
        );
    }

    private static void translate(KeyAst.File it) {
        it.accept(new Translator(outputDir));
    }

    public static String quote(String s) {
        return '"' + s + '"';
    }
}

class Translator extends KeYParserBaseVisitor<Void> {
    private final Path outputDir;
    private PrintWriter out;

    public Translator(Path outputDir) {
        this.outputDir = outputDir;
    }

    @Override
    public Void visitFile(KeYParser.FileContext ctx) {
        var name = new File(ctx.start.getTokenSource().getSourceName()).getName();
        final var classname = "_" + name.replace(".key", "");
        try (var out = new PrintWriter(Files.newBufferedWriter(outputDir.resolve(classname + ".java")))) {
            this.out = out;
            out.println("""
                    package de.uka.ilkd.key.proof.rulesc;
                    import java.util.List; 
                    import de.uka.ilkd.key.logic.NamespaceSet;
                    import de.uka.ilkd.key.java.Services;
                                                                                   
                    public class %s extends CompiledKeyFile {
                        public %s(Services services, NamespaceSet nss) { super(services, nss); }
                                      
                    """.formatted(classname,classname));
            super.visitFile(ctx);
            out.println("\n}");
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        return null;
    }

    @Override
    public Void visitSort_decls(KeYParser.Sort_declsContext ctx) {
        out.println("""
                public void declareSorts() {
                """);
        super.visitSort_decls(ctx);
        out.println("\n}\n");
        return null;
    }

    DeclarationBuilder decl = new DeclarationBuilder(new Services(JavaProfile.getDefaultProfile()), new NamespaceSet());

    @Override
    public Void visitProg_var_decls(KeYParser.Prog_var_declsContext ctx) {
        out.println("public void declareProgramVariables() {");
        for (int i = 0; i < ctx.simple_ident_comma_list().size(); i++) {
            List<String> varNames = decl.accept(ctx.simple_ident_comma_list(i));
            var kjt = ctx.keyjavatype(i);
            for (String varName : varNames) {
                out.format("""
                        declareProgramVariable("%s", "%s");
                        """, varName, kjt.toString());
            }
        }
        out.println("}");
        return null;
    }


    @Override
    public Void visitOption_decls(KeYParser.Option_declsContext ctx) {
        out.println("public void declareOptions() {");
        ctx.choice().forEach(it -> it.accept(this));
        out.println("}");
        return null;
    }

    @Override
    public Void visitChoice(KeYParser.ChoiceContext ctx) {
        String cat = ctx.category.getText();
        List<String> options;
        if (ctx.optionDecl().isEmpty()) {
            options = List.of("On", "Off");
        } else {
            options = ctx.optionDecl().stream().map(it -> it.IDENT.getText()).toList();
        }
        out.format("""
                declareChoice("%s", %s);
                """, cat, options.stream().map(it -> '"' + it + '"').collect(Collectors.joining(","))
        );
        return null;
    }

    @Override
    public Void visitOne_sort_decl(KeYParser.One_sort_declContext ctx) {
        List<String> sortOneOf =
                ctx.sortOneOf != null
                        ? ctx.sortOneOf.sortId().stream().map(RuleContext::getText).toList()
                        : List.of();
        List<String> sortExt =
                ctx.sortExt != null
                        ? ctx.sortExt.sortId().stream().map(RuleContext::getText).toList()
                        : List.of();
        boolean isGenericSort = ctx.GENERIC() != null;
        boolean isProxySort = ctx.PROXY() != null;
        boolean isAbstractSort = ctx.ABSTRACT() != null;
        var documentation = ParsingFacade.getValueDocumentation(ctx.DOC_COMMENT());
        for (var idCtx : ctx.sortIds.simple_ident_dots()) {
            String sortId = idCtx.getText();
            if (isGenericSort) {
                out.format("""
                        // %s
                        declareGenericSort("%s", "%s","%s");
                        """, BuilderHelpers.getPosition(idCtx), sortId, sortExt, sortOneOf);
            } else if (sortId.equals("any")) {
                continue;
                //skip
            } else if (isProxySort) {
                out.format("""
                        // %s
                        declareProxySort("%s", "%s");
                        """, BuilderHelpers.getPosition(idCtx), sortId, sortExt);
            } else {
                out.format("""
                        // %s
                        declareProxySort("%s", "%s", %s);
                        """, BuilderHelpers.getPosition(idCtx), sortId, sortExt, isAbstractSort);
            }
        }
        return null;
    }

    @Override
    public Void visitFunc_decls(KeYParser.Func_declsContext ctx) {
        out.println("public void declareFunctions() {");
        super.visitFunc_decls(ctx);
        out.println("}");
        return null;
    }

    @Override
    public Void visitPred_decls(KeYParser.Pred_declsContext ctx) {
        out.println("public void declarePredicates() {");
        super.visitPred_decls(ctx);
        out.println("}");
        return null;
    }

    @Override
    public Void visitPred_decl(KeYParser.Pred_declContext ctx) {
        String predName = ctx.funcpred_name().getText();
        String whereToBind = ctx.where_to_bind() != null
                ? ctx.whereToBind.getText()
                : "";

        String argSorts =
                ctx.arg_sorts().sortId().stream().map(RuleContext::getText)
                        .map(PreCompileKey::quote)
                        .collect(listOfJoining());

        /*if (whereToBind != null && whereToBind.size() != argSorts.size()) {
            semanticError(ctx, "Where-to-bind list must have same length as argument list");
        }*/

        int separatorIndex = predName.indexOf("::");
        if (separatorIndex > 0) {
            String sortName = predName.substring(0, separatorIndex);
            String baseName = predName.substring(separatorIndex + 2);
            out.format("""
                    declareSortDependeningPredicate("%s", "%s", %s, %s);
                    """, baseName, sortName, argSorts, whereToBind);

        } else {
            out.format("""
                    declarePredicate("%s", List.of(%s), List.of(%s));
                    """, predName, argSorts, whereToBind);
        }
        return null;
    }

    @Nonnull
    private static Collector<CharSequence, ?, String> listOfJoining() {
        return Collectors.joining(", ", "List.of(", ")");
    }

    @Override
    public Void visitFunc_decl(KeYParser.Func_declContext ctx) {
        out.println("{");
        boolean unique = ctx.UNIQUE() != null;
        var retSort = ctx.sortId().getText();
        String funcName = ctx.funcpred_name().getText();
        String whereToBind = ctx.where_to_bind() != null
                ? ctx.whereToBind.getText()
                : "";

        var argSorts = ctx.arg_sorts().sortId().stream().map(RuleContext::getText)
                .map(PreCompileKey::quote)
                .collect(listOfJoining());

        /*if (whereToBind != null && whereToBind.size() != argSorts.size()) {
            throw new IllegalStateException(BuilderHelpers.getPosition(ctx) + " Where-to-bind list must have same length as argument list");
        }*/

        int separatorIndex = funcName.indexOf("::");
        if (separatorIndex > 0) {
            String sortName = funcName.substring(0, separatorIndex);
            String baseName = funcName.substring(separatorIndex + 2);
            out.format("""
                    declareSortDependeningFunction("%s", "%s", List.of(%s), List.of(%s), %s);
                    """, baseName, sortName, argSorts, whereToBind, unique);

        } else {
            out.format("""
                    declareFunction("%s", "%s", %s, %s, %s);
                    """, funcName, retSort, argSorts, whereToBind, unique);
        }
        out.println("}");
        return null;
    }
}
