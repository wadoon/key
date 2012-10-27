package de.uka.ilkd.key.testgeneration;

import static org.junit.Assert.*;

import java.io.ByteArrayInputStream;

import org.junit.Before;
import org.junit.Test;

import antlr.DumpASTVisitor;
import antlr.RecognitionException;
import antlr.TokenStreamException;
import antlr.TreeParser;
import antlr.collections.AST;

import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYParser;

public class Sandbox {

    @Before
    public void setUp() throws Exception {
    }

    @Test
    public void test() throws RecognitionException, TokenStreamException {

        System.out.println(System.getProperty("key.rep"));
        System.out.println(System.getProperty("key.home"));
        System.out.println(System.getProperty("key.home") + "\n\n");
        
        for(Object prop : System.getProperties().keySet()){
            System.out.println(prop + "\t" + System.getProperty((String)prop));
        }
        
        
        for(String prop : System.getenv().keySet()){
            System.out.println(prop + "\t" + System.getenv(prop));
        }
        DefaultTermParser termParser = new DefaultTermParser();

        String example = "public class TestClass { int x = 0; }";

        ByteArrayInputStream stream = new ByteArrayInputStream(example.getBytes());
        KeYLexer lexer = new KeYLexer(stream);
        KeYParser parser = new KeYParser(lexer);
        
        System.out.println(parser.javaSource());
        
        System.out.println(parser.getAST().toStringTree());
    }

}
