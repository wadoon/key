package se.gu.svanefalk.tackey.editor.abstraction;

import java.io.File;
import java.io.InputStream;

import antlr.RecognitionException;
import antlr.TokenStreamException;
import antlr.collections.AST;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYParser;
import de.uka.ilkd.key.parser.ParserConfig;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.KeYFile;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.ui.ConsoleUserInterface;

public class ParserPlayground {

    /**
     * @param args
     * @throws ProofInputException
     * @throws TokenStreamException
     * @throws RecognitionException
     */
    public static void main(String[] args) throws ProofInputException,
            RecognitionException, TokenStreamException {

        File file = new File(
                "/home/christopher/runtime-EclipseApplication/KeYTest/test.key");
        //
        // RuleSource ruleSource = RuleSource.initRuleFile(input);
        //
        // ParserConfig pc = new ParserConfig(new Services(), new
        // NamespaceSet());
        //
        // KeYLexer lexer = new KeYLexer(ruleSource.getNewStream(), null);
        //
        // KeYParser problemParser = new KeYParser(ParserMode.TACLET, lexer,
        // ruleSource.toString(), pc, pc, null, null);
        //
        // problemParser.parseIncludes();
        // problemParser.parseFuncAndPred();
        // problemParser.parseFunctions();
        // problemParser.parsePredicates();
        // problemParser.parseProblem();
        // problemParser.parseRuleSets();
        // problemParser.parseSorts();
        // problemParser.parseTacletsAndProblem();
        // problemParser.parseVariables();
        // problemParser.parseWith();
        //
        // Includes includes = problemParser.getIncludes();
        // AST ast = problemParser.getAST();
        // int x = 1;

        
//        ConsoleUserInterface consoleUserInterface = new ConsoleUserInterface(
//                null, true);
//        KeYMediator mediator = new KeYMediator(consoleUserInterface);
//
//        ProblemLoader problemLoader = new ProblemLoader(file, null, null,
//                mediator);
//
//        KeYFile keYFile = new KeYFile(file.getName(), file,
//                consoleUserInterface);
//
//        Services services = new Services(mediator.getExceptionHandler());
//        ProblemInitializer problemInitializer = new ProblemInitializer(
//                consoleUserInterface, mediator.getProfile(), services, true,
//                consoleUserInterface);
//        InitConfig initConfig = problemInitializer.prepare(keYFile);

    }
}
