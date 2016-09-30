package de.tud.cs.se.ds.psec.parser;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.function.Function;

import org.antlr.v4.runtime.ANTLRFileStream;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.BailErrorStrategy;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.objectweb.asm.Label;

import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.Child_callContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.ConditionContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.DefinitionContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.InstructionContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.IntUnaryBytecodeInstrContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.LabelUnaryBytecodeInstrContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.Labeled_bytecode_instrContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.LocVarUnaryBytecodeInstrContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.Negated_load_instrContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.Nullary_bytecode_instrContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.Simple_expressionContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.Simple_load_instrContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.TranslationContext;
import de.tud.cs.se.ds.psec.parser.ast.ApplicabilityCheckInput;
import de.tud.cs.se.ds.psec.parser.ast.ApplicabilityCondition;
import de.tud.cs.se.ds.psec.parser.ast.ChildCall;
import de.tud.cs.se.ds.psec.parser.ast.Instruction;
import de.tud.cs.se.ds.psec.parser.ast.Instructions;
import de.tud.cs.se.ds.psec.parser.ast.IntegerUnaryBytecodeInstr;
import de.tud.cs.se.ds.psec.parser.ast.LabelUnaryBytecodeInstr;
import de.tud.cs.se.ds.psec.parser.ast.LabeledBytecodeInstr;
import de.tud.cs.se.ds.psec.parser.ast.LoadIntInstruction;
import de.tud.cs.se.ds.psec.parser.ast.LocVarUnaryBytecodeInstr;
import de.tud.cs.se.ds.psec.parser.ast.NullaryBytecodeInstr;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinition;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinitions;
import de.tud.cs.se.ds.psec.parser.ast.TranslationTacletASTElement;
import de.tud.cs.se.ds.psec.parser.exceptions.TranslationTacletInputException;

/**
 * Front-end for {@link TranslationTacletParser}, a parser for taclets defining
 * translations from Java SETs to bytecode. The recommended API elements for
 * starting the parser are {@link #parse(File)} and {@link #parse(String)}.
 * 
 * @author Dominic Scheurer
 */
public class TranslationTacletParserFE extends
        TranslationTacletParserBaseVisitor<TranslationTacletASTElement> {

    /**
     * The file that's being parsed. May be null if a String is being parsed.
     */
    private String fileName;

    /**
     * Map for remembering label objects by their name in the taclet definition.
     */
    private HashMap<String, Label> labelMap = new HashMap<>();

    private boolean bailAtError = false;

    // //////////////////////////////////////////// //
    // Constructors, public (convenience) interface //
    // //////////////////////////////////////////// //

    /**
     * @param bailAtError
     *            Set to true if the parsing process should stop and not try to
     *            recover in case of a syntax error in the parsed file.
     */
    public TranslationTacletParserFE(boolean bailAtError) {
        this.bailAtError = bailAtError;
    }

    /**
     * Initiates the parsing process for a file.
     *
     * @param file
     *            the file to parse.
     * @throws IOException
     *             if the file cannot be read.
     * @throws TranslationTacletInputException
     *             if an error occurs while parsing.
     * @return The parsed {@link TranslationDefinitions}.
     */
    public TranslationDefinitions parse(File file)
            throws IOException, TranslationTacletInputException {
        this.fileName = file.getAbsolutePath();

        // Create a CharStream that reads from an example file
        String fileName = file.getCanonicalPath();
        CharStream input = new ANTLRFileStream(fileName);

        return parse(input);
    }

    /**
     * Initiates the parsing process for a file.
     * 
     * @param inputStr
     *            the string to parse.
     * @throws TranslationTacletInputException
     *             if an error occurs while parsing.
     * @return The parsed {@link TranslationDefinitions}.
     */
    public TranslationDefinitions parse(String inputStr)
            throws TranslationTacletInputException {
        this.fileName = null;

        // Create a CharStream that reads from an the given input string
        CharStream input = new ANTLRInputStream(inputStr);

        return parse(input);
    }

    /**
     * Initiates the parsing process for a {@link URL}.
     * 
     * @param url
     *            the {@link URL} to parse from.
     * @throws TranslationTacletInputException
     *             if an error occurs while parsing.
     * @throws IOException
     *             If there's a problem by opening the resource from the
     *             {@link URL}.
     * @return The parsed {@link TranslationDefinitions}.
     */
    public TranslationDefinitions parse(URL url)
            throws TranslationTacletInputException, IOException {
        this.fileName = url.getFile();

        // Create a CharStream that reads from an the given input string
        CharStream input = new ANTLRInputStream(url.openStream());

        return parse(input);
    }

    /**
     * Parses from the given input stream.
     *
     * @param input
     *            the input stream to use for the parsing.
     * @throws TranslationTacletInputException
     *             if an error occurs while parsing.
     * @return The parsed {@link TranslationDefinitions}.
     */
    private TranslationDefinitions parse(CharStream input)
            throws TranslationTacletInputException {
        // Create the lexer
        TranslationTacletLexer lexer = new TranslationTacletLexer(input);

        // Create a buffer of tokens pulled from the lexer
        CommonTokenStream tokens = new CommonTokenStream(lexer);

        // Create the parser
        TranslationTacletParser parser = new TranslationTacletParser(tokens);

        // Bail at error
        if (bailAtError) {
            parser.setErrorHandler(new BailErrorStrategy());
        }

        // Traverse the parse tree
        try {
            ArrayList<TranslationDefinition> definitions = new ArrayList<>();
            parser.definitions().definition()
                    .forEach(defn -> definitions.add(visitDefinition(defn)));
            return new TranslationDefinitions(definitions);
        }
        catch (Exception e) {
            throw new TranslationTacletInputException(e.getMessage(), e);
        }
    }

    // /////////////////////////// //
    // Implemented visitor methods //
    // /////////////////////////// //

    @Override
    public TranslationDefinition visitDefinition(DefinitionContext ctx) {
        ArrayList<String> symbExTacletReferences = new ArrayList<>();
        ctx.taclets_reference().STRING_LITERAL()
                .forEach(s -> symbExTacletReferences
                        .add(s.getText().replaceAll("\"", "")));

        Function<ApplicabilityCheckInput, Boolean> applicabilityCheck = (input -> {
            return ctx.condition().stream()
                    .map(c -> visitCondition(c).isApplicable(input))
                    .reduce(true, (acc, c) -> acc && c);
        });

        return new TranslationDefinition(symbExTacletReferences,
                applicabilityCheck, visitTranslation(ctx.translation()));
    }

    @Override
    public ApplicabilityCondition visitCondition(ConditionContext ctx) {
        return visitSimple_expression(ctx.simple_expression());
    }

    @Override
    public ApplicabilityCondition visitSimple_expression(
            Simple_expressionContext ctx) {
        final String cmp = ctx.comparator().getText();
        final String metaVar = ctx.meta_var().getText();
        final int param2 = Integer.parseInt(ctx.integer().getText());

        // TODO it would be more efficient to do the case distinctions outside
        // the lambda and return simple lambdas. The checks will be done more
        // often than the parsing (in general).
        return new ApplicabilityCondition(info -> {
            int param1 = 0;

            switch (metaVar) {
            case "#num-children":
                param1 = info.getNumChildren();
                break;
            // Add support for more meta variables here. The parser should only
            // support Integer meta variables that are also specified here.
            }

            switch (cmp) {
            case "==":
                return param1 == param2;
            case "<=":
                return param1 <= param2;
            case ">=":
                return param1 >= param2;
            case "<":
                return param1 < param2;
            case ">":
                return param1 > param2;
            case "!=":
                return param1 != param2;
            default:
                return false;
            }
        });
    }

    @Override
    public Instructions visitTranslation(TranslationContext ctx) {
        // Reset the label map
        labelMap = new HashMap<>();
        
        ArrayList<Instruction> instructions = new ArrayList<>();
        ctx.instruction().forEach(i -> instructions.add(visitInstruction(i)));

        return new Instructions(instructions);
    }

    @Override
    public Instruction visitInstruction(InstructionContext ctx) {
        return (Instruction) super.visitInstruction(ctx);
    }

    @Override
    public LabeledBytecodeInstr visitLabeled_bytecode_instr(
            Labeled_bytecode_instrContext ctx) {
        return new LabeledBytecodeInstr(getLabelForName(ctx.LABEL().getText()),
                visit(ctx.bytecode_instr()));
    }

    @Override
    public NullaryBytecodeInstr visitNullary_bytecode_instr(
            Nullary_bytecode_instrContext ctx) {
        return new NullaryBytecodeInstr(ctx.getText());
    }

    @Override
    public LocVarUnaryBytecodeInstr visitLocVarUnaryBytecodeInstr(
            LocVarUnaryBytecodeInstrContext ctx) {
        return new LocVarUnaryBytecodeInstr(
                ctx.loc_var_unary_instrs().getText(), ctx.LOC_REF().getText());
    }

    @Override
    public LabelUnaryBytecodeInstr visitLabelUnaryBytecodeInstr(
            LabelUnaryBytecodeInstrContext ctx) {
        return new LabelUnaryBytecodeInstr(ctx.label_unary_instrs().getText(),
                getLabelForName(ctx.LABEL().getText()));
    }

    @Override
    public IntegerUnaryBytecodeInstr visitIntUnaryBytecodeInstr(
            IntUnaryBytecodeInstrContext ctx) {
        return new IntegerUnaryBytecodeInstr(
                ctx.int_const_unary_instrs().getText(),
                Integer.parseInt(ctx.integer().getText()));
    }

    @Override
    public LoadIntInstruction visitSimple_load_instr(
            Simple_load_instrContext ctx) {
        return new LoadIntInstruction(ctx.LOC_REF().getText(), false);
    }

    @Override
    public LoadIntInstruction visitNegated_load_instr(
            Negated_load_instrContext ctx) {
        return new LoadIntInstruction(ctx.LOC_REF().getText(), true);
    }

    @Override
    public ChildCall visitChild_call(Child_callContext ctx) {
        return new ChildCall(Integer.parseInt(ctx.NUMBER().getText()));
    }

    // //////////////////////// //
    // Exception helper methods //
    // //////////////////////// //

    // ///////////////////////////// //
    // Miscellaneous private methods //
    // ///////////////////////////// //

    /**
     * Returns the label associated with the given name.
     * 
     * @param labelName
     *            The name of the label, e.g. "l0".
     * @return The label for the given label name.
     */
    private Label getLabelForName(String labelName) {
        Label result = null;

        if (labelMap.containsKey(labelName)) {
            result = labelMap.get(labelName);
        }
        else {
            result = new Label();
            labelMap.put(labelName, result);
        }

        return result;
    }

    /**
     * @return The file name of the file being parsed; a fallback String, if no
     *         file is given (i.e. a String is parsed).
     */
    @SuppressWarnings("unused")
    private String getFileName() {
        // TODO This method should be used to provide useful feedback.
        String fallback = "<no file given>";

        if (fileName == null) {
            return fallback;
        }
        else {
            return fileName;
        }
    }
}
