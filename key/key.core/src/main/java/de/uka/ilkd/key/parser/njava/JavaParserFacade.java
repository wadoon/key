package de.uka.ilkd.key.parser.njava;

import de.uka.ilkd.key.nparser.JavaKLexer;
import de.uka.ilkd.key.nparser.JavaKParser;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Token;
import recoder.java.Comment;
import recoder.java.CompilationUnit;
import recoder.java.SingleLineComment;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (10/12/20)
 */
public class JavaParserFacade {
    public static CompilationUnit parseCompilationUnit(CharStream stream) {
        ASTList<Comment> comments = getCommentTokens(stream);
        JavaKParser.CompilationUnitContext unit = createParser(stream).compilationUnit();
        JavaKBuilder builder = new JavaKBuilder();
        CompilationUnit cu = (CompilationUnit) unit.accept(builder);
        cu.setComments(comments);
        return cu;
    }

    private static ASTList<Comment> getCommentTokens(CharStream stream) {
        ASTList<Comment> seq = new ASTArrayList<>();
        JavaKLexer lexer = createLexer(stream);
        CommonTokenStream commentStream = new CommonTokenStream(lexer, JavaKLexer.HIDDEN);
        Token token = commentStream.get(1);
        do {
            if (token.getType() == JavaKLexer.LINE_COMMENT){
                Comment c = new SingleLineComment(token.getText());
                seq.add(c);
            }
            if(token.getType() == JavaKLexer.COMMENT) {
                Comment c = new Comment(token.getText());
                seq.add(c);
            }
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
}
