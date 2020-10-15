package de.uka.ilkd.key.parser.njava;

import antlr.ASTNULLType;
import de.uka.ilkd.key.nparser.JavaKLexer;
import de.uka.ilkd.key.nparser.JavaKParser;
import org.antlr.v4.runtime.*;
import recoder.java.Comment;
import recoder.java.CompilationUnit;
import recoder.java.SingleLineComment;
import recoder.java.SourceElement;
import recoder.java.declaration.FieldDeclaration;
import recoder.java.declaration.MemberDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (10/12/20)
 */
public class JavaParserFacade {

    private static SourceElement translate(ParserRuleContext ctx) {
        JavaKBuilder builder = new JavaKBuilder();
        SourceElement obj = (SourceElement) ctx.accept(builder);
        return obj;
    }

    public static CompilationUnit parseCompilationUnit(CharStream stream) {
        //ASTList<Comment> comments = getCommentTokens(stream);
        JavaKParser.CompilationUnitContext unit = createParser(stream).compilationUnit();
        CompilationUnit cu = (CompilationUnit) translate(unit);
        //cu.setComments(comments);
        return cu;
    }

    private static ASTList<Comment> getCommentTokens(CharStream stream) {
        ASTList<Comment> seq = new ASTArrayList<>();
        JavaKLexer lexer = createLexer(stream);
        CommonTokenStream commentStream = new CommonTokenStream(lexer, JavaKLexer.HIDDEN);
        commentStream.fill();
        Token token;
        do {
            token = commentStream.LT(1);
            if (token.getType() == JavaKLexer.LINE_COMMENT){
                Comment c = new SingleLineComment(token.getText());
                seq.add(c);
            }
            if(token.getType() == JavaKLexer.COMMENT) {
                Comment c = new Comment(token.getText());
                seq.add(c);
            }
            if(token.getType()!=Token.EOF)
                commentStream.consume();
        } while (token.getType() != Token.EOF);
        return seq;
    }

    public static  JavaKParser.CompilationUnitContext parseFile(CharStream stream) {
        return createParser(stream).compilationUnit();
    }

    public static JavaKParser createParser(CharStream stream) {
        JavaKParser parser = new JavaKParser(new CommonTokenStream(createLexer(stream)));
        return parser;
    }

    public static JavaKLexer createLexer(CharStream stream) {
        JavaKLexer lexer = new JavaKLexer(stream);
        return lexer;
    }

    public static FieldDeclaration parseFieldDeclaration(CharStream stream) {
        return null;
    }

    public static MemberDeclaration parseMemberDeclaration(CharStream stream) {
        return null;
    }

    public static MethodDeclaration parseMethodDeclaration(CharStream stream) {
        return null;
    }

    public static SourceElement parseStatementBlock(CharStream stream) {
        return translate(createParser(stream).block());
    }
}
