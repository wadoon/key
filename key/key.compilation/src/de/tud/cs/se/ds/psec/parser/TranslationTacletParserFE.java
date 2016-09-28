package de.tud.cs.se.ds.psec.parser;

import java.io.File;
import java.io.IOException;

import org.antlr.v4.runtime.ANTLRFileStream;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.BailErrorStrategy;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;

import de.uka.ilkd.key.proof.init.ProofInputException;

/**
 * Front-end for {@link TranslationTacletParser}, a parser for taclets defining
 * translations from Java SETs to bytecode.
 * 
 * @author Dominic Scheurer
 */
public class TranslationTacletParserFE
        extends TranslationTacletParserBaseVisitor<Object> {

    /**
     * The file that's being parsed. May be null if a String is being parsed.
     */
    private File file;

    // //////////////////////////////////////////// //
    // Constructors, public (convenience) interface //
    // //////////////////////////////////////////// //

    /**
     * Initiates the parsing process for a file.
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
     * Initiates the parsing process for a file.
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
        TranslationTacletLexer lexer = new TranslationTacletLexer(input);

        // Create a buffer of tokens pulled from the lexer
        CommonTokenStream tokens = new CommonTokenStream(lexer);

        // Create the parser
        TranslationTacletParser parser = new TranslationTacletParser(tokens);

        // Bail at error
        parser.setErrorHandler(new BailErrorStrategy());

        // Traverse the parse tree
        try {
            visit(parser.definitions());
        }
        catch (Exception e) {
            throw new ProofInputException(e.getMessage(), e);
        }
    }

    // /////////////////////////// //
    // Implemented visitor methods //
    // /////////////////////////// //

    // //////////////////////// //
    // Exception helper methods //
    // //////////////////////// //

    // ///////////////////////////// //
    // Miscellaneous private methods //
    // ///////////////////////////// //

    /**
     * @return The file name of the file being parsed; a fallback String, if no
     *         file is given (i.e. a String is parsed).
     */
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
