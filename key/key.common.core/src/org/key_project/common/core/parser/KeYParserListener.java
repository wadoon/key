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

import java.io.IOException;

import org.antlr.v4.runtime.ANTLRFileStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeProperty;
import org.antlr.v4.runtime.tree.ParseTreeWalker;
import org.key_project.common.core.parser.KeYCommonParser.*;
import org.key_project.util.collection.ImmutableList;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class KeYParserListener extends KeYCommonParserBaseListener {
    
    private ParseTreeProperty<String> strValues = new ParseTreeProperty<>();
    private ParseTreeProperty<ImmutableList<String>> strListValues = new ParseTreeProperty<>();
    
    private void setValue(ParseTree node, String value) {
        strValues.put(node, value);
    }
    
    private String getValueStr(ParseTree node) {
        return strValues.get(node);
    }
    
    private void setValue(ParseTree node, ImmutableList<String> value) {
        strListValues.put(node, value);
    }
    
    private ImmutableList<String> getValueStrList(ParseTree node) {
        return strListValues.get(node);
    }

    @Override
    public void exitDecls(DeclsContext ctx) {
        // TODO Auto-generated method stub
        
    }

    @Override
    public void exitSort_decls(Sort_declsContext ctx) {
        // TODO Auto-generated method stub
        System.out.println(ctx.getText());
        System.out.println(ctx.multipleSorts.children.size());
        // XXX Check how we can obtain all 5 (!) sort decls in integerHeader
        // Shows only 4 children, but there are 5.
    }

    @Override
    public void exitPred_decls(Pred_declsContext ctx) {
        // TODO Auto-generated method stub
        
    }

    @Override
    public void exitFunc_decls(Func_declsContext ctx) {
        // TODO Auto-generated method stub
        
    }

    @Override
    public void exitOne_sort_decl(One_sort_declContext ctx) {
        // TODO Auto-generated method stub
        
    }

    @Override
    public void exitPred_decl(Pred_declContext ctx) {
        // TODO Auto-generated method stub
        
    }

    @Override
    public void exitFunc_decl(Func_declContext ctx) {
        // TODO Auto-generated method stub
        
    }

    @Override
    public void exitExtends_sorts(Extends_sortsContext ctx) {
        // TODO Auto-generated method stub
        
    }

    @Override
    public void exitOneof_sorts(Oneof_sortsContext ctx) {
        // TODO Auto-generated method stub
        
    }

    @Override
    public void exitArg_sorts_or_formula(Arg_sorts_or_formulaContext ctx) {
        // TODO Auto-generated method stub
        
    }

    @Override
    public void exitArg_sorts(Arg_sortsContext ctx) {
        // TODO Auto-generated method stub
        
    }

    @Override
    public void exitWhere_to_bind(Where_to_bindContext ctx) {
        // TODO Auto-generated method stub
        
    }
    
    @Override
    public void exitGenericFunctionName(GenericFunctionNameContext ctx) {
        setValue(ctx, getValueStr(ctx.prefix) + "::" + getValueStr(ctx.name));
    }
    
    @Override
    public void exitSimpleIdentFunctionName(SimpleIdentFunctionNameContext ctx) {
        setValue(ctx, getValueStr(ctx.name));
    }
    
    @Override
    public void exitDigitFunctionName(DigitFunctionNameContext ctx) {
        setValue(ctx, ctx.getText());
    }

    @Override
    public void exitSortId(SortIdContext ctx) {
        // TODO Auto-generated method stub
        
    }

    @Override
    public void exitSort_name(Sort_nameContext ctx) {
        setValue(ctx, ctx.getText());
    }

    @Override
    public void exitSimple_ident_dots(Simple_ident_dotsContext ctx) {
        setValue(ctx, ctx.getText());
    }

    @Override
    public void exitSimple_ident_comma_list(Simple_ident_comma_listContext ctx) {
        // TODO Auto-generated method stub
    }

    @Override
    public void exitSimple_ident(Simple_identContext ctx) {
        setValue(ctx, ctx.getText());
    }
    
    public static void main(String[] args) throws IOException {
        CharStream input = new ANTLRFileStream("resources/org/key_project/common/core/proof/rules/integerHeader.key");
        KeYCommonLexer lexer = new KeYCommonLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        KeYCommonParser parser = new KeYCommonParser(tokens);
        KeYCommonParser.DeclsContext tree = parser.decls();
        
        KeYParserListener listener = new KeYParserListener();
        ParseTreeWalker.DEFAULT.walk(listener, tree);
    }

}
