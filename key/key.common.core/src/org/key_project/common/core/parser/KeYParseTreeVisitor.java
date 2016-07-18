// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package org.key_project.common.core.parser;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.antlr.v4.runtime.*;
import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.Namespace;
import org.key_project.common.core.logic.NamespaceSet;
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.op.SortDependingFunction;
import org.key_project.common.core.logic.sort.*;
import org.key_project.common.core.parser.KeYCommonParser.*;
import org.key_project.common.core.parser.exceptions.*;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Pair;

/**
 * Front-end for {@link KeYCommonParser}, a parser for PL-independent KeY input
 * files. Currently, sort, predicate and function declarations are parsed.
 * <p>
 * NOTE: Passes the tests in <code>TestDeclParser</code>, but may still have
 * some problems, especially things like a {@link GenericSortException} that
 * should be thrown, but isn't.
 *
 * @author Dominic Scheurer
 */
public class KeYParseTreeVisitor extends KeYCommonParserBaseVisitor<Object> {
    private final NamespaceSet nss;
    private File file;

    // //////////////////////////////////////////// //
    // Constructors, public (convenience) interface //
    // //////////////////////////////////////////// //

    /**
     * Constructs a parser with empty {@link NamespaceSet}.
     */
    public KeYParseTreeVisitor() {
        this.nss = new NamespaceSet();
    }

    /**
     * Constructs a parser which adds new elements to the given
     * {@link NamespaceSet}.
     *
     * @param nss
     *            The {@link NamespaceSet} to add parsed elements to.
     */
    public KeYParseTreeVisitor(NamespaceSet nss) {
        this.nss = nss;
    }

    /**
     * Initiates the parsing process for a file. Afterward, methods like
     * {@link #sorts()} should return sensible results.
     *
     * @param file
     *            the file to parse.
     * @throws IOException
     *             if the file cannot be read.
     * @throws ProofInputException
     *             if an error occurs while parsing.
     */
    public void parse(File file) throws IOException, ProofInputException {
        this.file = file;

        // Create a CharStream that reads from an example file
        String fileName = file.getCanonicalPath();
        CharStream input = new ANTLRFileStream(fileName);

        parse(input);
    }

    /**
     * Initiates the parsing process for a file. Afterward, methods like
     * {@link #sorts()} should return sensible results.
     * 
     * @param inputStr
     *            the string to parse.
     * @throws ProofInputException
     *             if an error occurs while parsing.
     */
    public void parse(String inputStr) throws ProofInputException {
        this.file = null;

        // Create a CharStream that reads from an the given input string
        CharStream input = new ANTLRInputStream(inputStr);

        parse(input);
    }

    /**
     * Parses from the given input stream.
     *
     * @param input
     *            the input stream to use for the parsing.
     * @throws ProofInputException
     *             if an error occurs while parsing.
     */
    private void parse(CharStream input) throws ProofInputException {
        // Create the lexer
        KeYCommonLexer lexer = new KeYCommonLexer(input);

        // Create a buffer of tokens pulled from the lexer
        CommonTokenStream tokens = new CommonTokenStream(lexer);

        // Create the parser
        KeYCommonParser parser = new KeYCommonParser(tokens);

        // Traverse the parse tree
        try {
            visit(parser.decls());
        }
        catch (Exception e) {
            throw new ProofInputException(e.getMessage(), e);
        }
    }

    /**
     * Call {@link #parse()} before using this method.
     * 
     * @return the {@link NamespaceSet} containing the parsed contents.
     */
    public NamespaceSet getNss() {
        return nss;
    }

    /**
     * Call {@link #parse()} before using this method.
     *
     * @return The parsed {@link Sort} declarations.
     */
    public Namespace sorts() {
        return nss.sorts();
    }

    /**
     * Call {@link #parse()} before using this method.
     *
     * @return The parsed {@link Function} declarations.
     */
    public Namespace functions() {
        return nss.functions();
    }

    // /////////////////////////// //
    // Implemented visitor methods //
    // /////////////////////////// //

    @Override
    public Function visitPred_decl(Pred_declContext ctx) {

        Function p = null;

        final ImmutableArray<Boolean> whereToBind = visitWhere_to_bind(ctx.where_to_bind());
        final ImmutableArray<Sort> argSorts = visitArg_sorts(ctx.arg_sorts());

        if (whereToBind != null && whereToBind.size() != argSorts.size()) {
            semanticExc("Where-to-bind list must have same length as argument list", ctx);
        }

        if (ctx.pred_name instanceof GenericFunctionNameContext) {
            final Pair<String, String> sortAndFctName =
                    visitGenericFunctionName((GenericFunctionNameContext) ctx.pred_name);

            final Sort genSort = (Sort) sorts().lookup(sortAndFctName.first);

            if (genSort == null) {
                notDeclExc("Sort", sortAndFctName.first, ctx);
            }

            if (!(genSort instanceof CCGenericSort)) {
                semanticExc("Generic function must depend on generic sort", ctx);
            }

            p = SortDependingFunction.createFirstInstance(
                    (CCGenericSort) genSort,
                    new Name(sortAndFctName.second),
                    Sort.FORMULA,
                    argSorts.toArray(new Sort[argSorts.size()]),
                    false,
                    SortImpl.ANY);

        }
        else {
            String funcName = null;

            if (ctx.pred_name instanceof SimpleIdentFunctionNameContext) {
                funcName = visitSimpleIdentFunctionName((SimpleIdentFunctionNameContext) ctx.pred_name);
            }
            else if (ctx.pred_name instanceof DigitFunctionNameContext) {
                funcName = visitDigitFunctionName((DigitFunctionNameContext) ctx.pred_name);
            }

            p = new Function(new Name(funcName), Sort.FORMULA, argSorts, whereToBind, false);
        }

        if (functions().lookup(p.name()) != null) {
            ambiguousDeclExc(p.name().toString(), ctx.pred_name);
        }

        functions().add(p);
        return p;
    }

    @Override
    public Function visitFunc_decl(Func_declContext ctx) {
        Function f = null;

        final boolean unique = ctx.UNIQUE() != null;
        final String retSortName = visitSort_name(ctx.sort_name());
        final Sort retSort = (Sort) sorts().lookup(retSortName);
        final ImmutableArray<Boolean> whereToBind = visitWhere_to_bind(ctx.where_to_bind());
        final ImmutableArray<Sort> argSorts = visitArg_sorts(ctx.arg_sorts());

        if (retSort == null) {
            notDeclExc("Sort", retSortName, ctx);
        }

        if (whereToBind != null && whereToBind.size() != argSorts.size()) {
            semanticExc("Where-to-bind list must have same length as argument list", ctx);
        }

        if (ctx.func_name instanceof GenericFunctionNameContext) {
            final Pair<String, String> sortAndFctName =
                    visitGenericFunctionName((GenericFunctionNameContext) ctx.func_name);

            final Sort genSort = (Sort) sorts().lookup(sortAndFctName.first);

            if (genSort == null) {
                notDeclExc("Sort", sortAndFctName.first, ctx);
            }

            if (!(genSort instanceof CCGenericSort)) {
                semanticExc("Generic function must depend on generic sort", ctx);
            }

            f = SortDependingFunction.createFirstInstance(genSort, new Name(sortAndFctName.second), retSort,
                    argSorts.toArray(new Sort[argSorts.size()]),
                    unique, SortImpl.ANY);

        }
        else {
            String funcName = null;

            if (ctx.func_name instanceof SimpleIdentFunctionNameContext) {
                funcName = visitSimpleIdentFunctionName((SimpleIdentFunctionNameContext) ctx.func_name);
            }
            else if (ctx.func_name instanceof DigitFunctionNameContext) {
                funcName = visitDigitFunctionName((DigitFunctionNameContext) ctx.func_name);
            }

            f = new Function(new Name(funcName), retSort, argSorts, whereToBind, unique);
        }

        if (functions().lookup(f.name()) != null) {
            ambiguousDeclExc(f.name().toString(), ctx.func_name);
        }

        functions().add(f);
        return f;
    }

    /**
     * Returns the list of specified sorts and adds each to the sorts namespace.
     */
    @Override
    public ArrayList<Sort> visitComma_sort_decl(Comma_sort_declContext ctx) {
        ArrayList<Sort> result = new ArrayList<>();
        for (String sortName : visitSimple_ident_comma_list(ctx.simple_ident_comma_list())) {
            if (sorts().lookup(sortName) == null) {
                Sort s = new SortImpl(new Name(sortName));
                result.add(s);
                sorts().add(s);
            }
        }
        return result;
    }

    @Override
    public ArrayList<CCGenericSort> visitGeneric_sort_decl(Generic_sort_declContext ctx) {
        try {
            ArrayList<CCGenericSort> result = new ArrayList<>();

            for (Simple_identContext context : ctx.sortIds.simple_ident()) {
                String sortName = visitSimple_ident(context);

                if (sorts().lookup(sortName) == null) {
                    CCGenericSort s = new CCGenericSort(new Name(sortName),
                            visitExtends_sorts(ctx.extends_sorts()),
                            visitOneof_sorts(ctx.oneof_sorts()));

                    sorts().add(s);
                    result.add(s);
                }
            }

            return result;
        }
        catch (GenericSupersortException e) {
            throw new GenericSortException("sort", "Illegal sort given", e.getIllegalSort(), getFileName(),
                    ctx.getStart().getLine(), ctx.getStart().getCharPositionInLine());
        }
    }

    @Override
    public ArrayList<ProxySort> visitProxy_sort_decl(Proxy_sort_declContext ctx) {
        ArrayList<ProxySort> result = new ArrayList<>();

        for (Simple_identContext context : ctx.sortIds.simple_ident()) {
            String sortName = visitSimple_ident(context);

            if (sorts().lookup(sortName) == null) {
                ProxySort s = new ProxySort(new Name(sortName),
                        visitExtends_sorts(ctx.extends_sorts()));

                sorts().add(s);
                result.add(s);
            }
        }

        return result;
    }

    @Override
    public Sort visitExtends_sort_decl(Extends_sort_declContext ctx) {
        return new SortImpl(new Name(visitSimple_ident(ctx.simple_ident())),
                visitExtends_sorts(ctx.extends_sorts()));
    }

    @Override
    public ImmutableSet<Sort> visitExtends_sorts(Extends_sortsContext ctx) {
        ImmutableSet<Sort> sortIds = DefaultImmutableSet.<Sort>nil();

        if (ctx == null) {
            // No \extends_sorts given
            return DefaultImmutableSet.<Sort>nil().add(SortImpl.ANY);
        }

        for (Simple_ident_dotsContext context : ctx.simple_ident_dots()) {
            String sortName = visitSimple_ident_dots(context);

            if (sortName.equals("any")) {
                sortIds = sortIds.add(SortImpl.ANY);
            }
            else {
                Sort sort = (Sort) sorts().lookup(sortName);
                if (sort == null) {
                    throw new NotDeclException(getFileName(), ctx.start.getLine(), ctx.start.getCharPositionInLine(),
                            "Sort", sortName);
                }
                sortIds = sortIds.add(sort);
            }
        }

        return sortIds;
    }

    @Override
    public ImmutableSet<Sort> visitOneof_sorts(Oneof_sortsContext ctx) {
        if (ctx != null) {
            return DefaultImmutableSet.<Sort>nil().add(collectSorts(ctx.sortId(), ctx, true));
        }
        else {
            // No \oneof given
            return DefaultImmutableSet.<Sort>nil();
        }
    }

    @Override
    public ImmutableArray<Sort> visitArg_sorts(Arg_sortsContext ctx) {
        ArrayList<Sort> result = collectSorts(ctx.sortId(), ctx, false);

        if (result == null) {
            return null;
        }

        return new ImmutableArray<>(collectSorts(ctx.sortId(), ctx, false));
    }

    // ////////////////////////////////////////// //
    // "Primitive" visitor methods only returning
    // (collections of) primitive data types.
    // ////////////////////////////////////////// //

    @Override
    public ImmutableArray<Boolean> visitWhere_to_bind(Where_to_bindContext ctx) {
        ArrayList<Boolean> result = new ArrayList<>();

        if (ctx == null) {
            return null;
        }

        for (Boolean_valueContext context : ctx.boolean_value()) {
            result.add(visitBoolean_value(context));
        }

        return new ImmutableArray<>(result);
    }

    @Override
    public Boolean visitBoolean_value(Boolean_valueContext ctx) {
        return ctx.FALSE() == null ? true : false;
    }

    @Override
    public Pair<String, String> visitGenericFunctionName(GenericFunctionNameContext ctx) {
        return new Pair<>(visitSort_name(ctx.prefix), visitSimple_ident(ctx.name));
    }

    @Override
    public String visitSimpleIdentFunctionName(SimpleIdentFunctionNameContext ctx) {
        return visitSimple_ident(ctx.name);
    }

    @Override
    public String visitDigitFunctionName(DigitFunctionNameContext ctx) {
        return visitDigit(ctx.name);
    }

    @Override
    public String visitDigit(DigitContext ctx) {
        return ctx.getText();
    }

    @Override
    public String visitSortId(SortIdContext ctx) {
        return ctx.getText();
    }

    @Override
    public String visitSort_name(Sort_nameContext ctx) {
        return ctx.getText();
    }

    @Override
    public ArrayList<String> visitSimple_ident_comma_list(Simple_ident_comma_listContext ctx) {
        ArrayList<String> result = new ArrayList<>();
        for (Simple_identContext simpleIdent : ctx.simple_ident()) {
            result.add(visitSimple_ident(simpleIdent));
        }
        return result;
    }

    @Override
    public String visitSimple_ident_dots(Simple_ident_dotsContext ctx) {
        return ctx.getText();
    }

    @Override
    public String visitSimple_ident(Simple_identContext ctx) {
        return ctx.getText();
    }

    // //////////////////////// //
    // Exception helper methods //
    // //////////////////////// //

    private void semanticExc(String message, ParserRuleContext ctx) {
        throw new KeYSemanticException(getFileName(), message, ctx.start.getLine(), ctx.start.getCharPositionInLine());
    }

    private void notDeclExc(String category, String undeclaredSymbol, ParserRuleContext ctx) {
        throw new NotDeclException(getFileName(), ctx.start.getLine(), ctx.start.getCharPositionInLine(),
                category, undeclaredSymbol);
    }

    private void ambiguousDeclExc(String ambiguousSymbol, ParserRuleContext ctx) {
        throw new AmbiguousDeclException(getFileName(), ctx.start.getLine(), ctx.start.getCharPositionInLine(),
                ambiguousSymbol);
    }

    private void assertNonGeneric(Sort s, ParserRuleContext ctx) {
        if (s instanceof CCGenericSort) {
            throw new GenericSortException(
                    "sort",
                    "Non-generic sort expected",
                    s,
                    getFileName(),
                    ctx.start.getLine(),
                    ctx.start.getCharPositionInLine());
        }
    }

    // ///////////////////////////// //
    // Miscellaneous private methods //
    // ///////////////////////////// //

    private ArrayList<Sort> collectSorts(List<SortIdContext> sorts, ParserRuleContext ctx, boolean checkNonGeneric) {
        ArrayList<Sort> sortIds = new ArrayList<>();
        for (SortIdContext context : sorts) {
            String sortName = visitSortId(context);
            Sort sort = (Sort) sorts().lookup(sortName);

            if (sort == null) {
                throw new NotDeclException(getFileName(), ctx.start.getLine(), ctx.start.getCharPositionInLine(),
                        "Sort", sortName);
            }

            if (checkNonGeneric) {
                assertNonGeneric(sort, ctx);
            }

            sortIds.add(sort);
        }
        return sortIds;
    }

    private String getFileName() {
        String fallback = "<no file given>";

        if (file == null) {
            return fallback;
        }
        else {
            return file.getName();
        }
    }

}