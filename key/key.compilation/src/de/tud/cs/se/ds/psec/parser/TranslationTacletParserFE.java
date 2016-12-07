package de.tud.cs.se.ds.psec.parser;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Optional;
import java.util.function.Function;

import org.antlr.v4.runtime.ANTLRFileStream;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.BailErrorStrategy;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;

import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.ArithmeticExpressionAtomContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.Child_callContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.ConditionContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.DefinitionContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.Field_instrContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.GetUppermostLoopEntryLabelContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.GetUppermostLoopExitLabelContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.InstructionContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.IntUnaryBytecodeInstrContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.Invoke_instr_literalContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.Invoke_instr_svContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.IsConstructorExpressionContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.IsFieldReferenceContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.IsResultVarExpressionContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.IsStaticExpressionContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.IsSuperMethodContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.IsValidInStateExpressionContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.IsVoidExpressionContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.LabelUnaryBytecodeInstrContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.Labeled_bytecode_instrContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.LocVarUnaryBytecodeInstrContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.Negated_load_instrContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.Nullary_bytecode_instrContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.Params_load_instrContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.PopLoopEntryLabelContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.PopLoopExitLabelContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.PushLoopEntryLabelContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.PushLoopExitLabelContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.SimpleTypeExpressionContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.Simple_arithmetic_expressionContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.Simple_load_instrContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.SpecialExpressionAtomContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.SpecialLabelUnaryBytecodeInstrContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.SpecialUnaryInstrsContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.Store_instrContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.StringLitUnaryBytecodeInstrContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.Super_callContext;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParser.TranslationContext;
import de.tud.cs.se.ds.psec.parser.ast.ApplicabilityCheckInput;
import de.tud.cs.se.ds.psec.parser.ast.ApplicabilityCondition;
import de.tud.cs.se.ds.psec.parser.ast.ChildCall;
import de.tud.cs.se.ds.psec.parser.ast.FieldInstr;
import de.tud.cs.se.ds.psec.parser.ast.Instruction;
import de.tud.cs.se.ds.psec.parser.ast.Instructions;
import de.tud.cs.se.ds.psec.parser.ast.IntegerUnaryBytecodeInstr;
import de.tud.cs.se.ds.psec.parser.ast.InvokeInstr;
import de.tud.cs.se.ds.psec.parser.ast.LabelUnaryBytecodeInstr;
import de.tud.cs.se.ds.psec.parser.ast.LabeledBytecodeInstr;
import de.tud.cs.se.ds.psec.parser.ast.LdcInstr;
import de.tud.cs.se.ds.psec.parser.ast.LoadInstruction;
import de.tud.cs.se.ds.psec.parser.ast.LocVarUnaryBytecodeInstr;
import de.tud.cs.se.ds.psec.parser.ast.LoopLabelInstruction;
import de.tud.cs.se.ds.psec.parser.ast.NullaryBytecodeInstr;
import de.tud.cs.se.ds.psec.parser.ast.ParamsLoadInstruction;
import de.tud.cs.se.ds.psec.parser.ast.StoreInstruction;
import de.tud.cs.se.ds.psec.parser.ast.StringTranslationTacletASTElement;
import de.tud.cs.se.ds.psec.parser.ast.SuperCallInstruction;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinition;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinitions;
import de.tud.cs.se.ds.psec.parser.ast.TranslationTacletASTElement;
import de.tud.cs.se.ds.psec.parser.ast.TypeInstr;
import de.tud.cs.se.ds.psec.parser.exceptions.TranslationTacletInputException;
import de.tud.cs.se.ds.psec.util.LogicUtils;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.declaration.ConstructorDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;

/**
 * Front-end for {@link TranslationTacletParser}, a parser for taclets defining
 * translations from Java SETs to bytecode. The recommended API elements for
 * starting the parser are {@link #parse(File)} and {@link #parse(String)}.
 * 
 * @author Dominic Scheurer
 */
public class TranslationTacletParserFE extends
        TranslationTacletParserBaseVisitor<TranslationTacletASTElement> {

    public static final String UPPERMOST_LOOP_EXIT_SPECIAL_LBL = "<<UPPERMOST_LOOP_EXIT>>";
    public static final String UPPERMOST_LOOP_ENTRY_SPECIAL_LBL = "<<UPPERMOST_LOOP_ENTRY>>";

    /**
     * The file that's being parsed. May be null if a String is being parsed.
     */
    private String fileName;

    /**
     * Map for making label references in definitions unique
     */
    private HashMap<String, String> labelMap = new HashMap<>();
    private int labelCounter = 0;

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
        } catch (Exception e) {
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

        return new TranslationDefinition(ctx.name.getText(),
                symbExTacletReferences, applicabilityCheck,
                visitTranslation(ctx.translation()));
    }

    @Override
    public ApplicabilityCondition visitCondition(ConditionContext ctx) {
        return (ApplicabilityCondition) visit(ctx.expression_atom());
    }

    @Override
    public ApplicabilityCondition visitArithmeticExpressionAtom(
            ArithmeticExpressionAtomContext ctx) {
        if (ctx.NOT() == null) {
            return (ApplicabilityCondition) visit(
                    ctx.simple_arithmetic_expression());
        } else {
            final ApplicabilityCondition subCondition = (ApplicabilityCondition) visit(
                    ctx.simple_arithmetic_expression());
            return new ApplicabilityCondition(info -> {
                return !subCondition.isApplicable(info);
            });
        }
    }

    @Override
    public ApplicabilityCondition visitSpecialExpressionAtom(
            SpecialExpressionAtomContext ctx) {
        if (ctx.NOT() == null) {
            return (ApplicabilityCondition) visit(ctx.special_expression());
        } else {
            final ApplicabilityCondition subCondition = (ApplicabilityCondition) visit(
                    ctx.special_expression());
            return new ApplicabilityCondition(info -> {
                return !subCondition.isApplicable(info);
            });
        }
    }

    @Override
    public ApplicabilityCondition visitSimpleTypeExpression(
            SimpleTypeExpressionContext ctx) {
        return new ApplicabilityCondition(info -> {
            Expression expr = (Expression) info.getInstantiations()
                    .getInstantiationFor(ctx.LOC_REF().getText()).get();

            return LogicUtils.isSimpleExpression(expr, info.getServices());
        });
    }
    
    @Override
    public ApplicabilityCondition visitIsSuperMethod(IsSuperMethodContext ctx) {
        return new ApplicabilityCondition(info -> {
            IProgramMethod pm = (IProgramMethod) info.getInstantiations()
                    .getInstantiationFor(ctx.called_method.getText()).get();
            IProgramMethod methodBeingCompiled = (IProgramMethod) info
                    .getInstantiations()
                    .getInstantiationFor(ctx.compiled_method.getText()).get();

            return !methodBeingCompiled.getContainerType().getSort()
                    .equals(pm.getContainerType().getSort())
                    && methodBeingCompiled.getContainerType().getSort()
                            .extendsTrans(pm.getContainerType().getSort());
        });
    }

    @Override
    public ApplicabilityCondition visitIsConstructorExpression(
            IsConstructorExpressionContext ctx) {
        return new ApplicabilityCondition(info -> {
            Object method = info.getInstantiations()
                    .getInstantiationFor(ctx.LOC_REF().getText()).get();

            if (method instanceof MethodName) {
                MethodName mName = (MethodName) method;
                return mName.toString().equals("<init>");
            }

            MethodDeclaration methodDeclaration = null;
            if (method instanceof MethodBodyStatement) {
                methodDeclaration = ((MethodBodyStatement) method)
                        .getProgramMethod(info.getServices())
                        .getMethodDeclaration();
            } else if (method instanceof ProgramMethod) {
                methodDeclaration = ((ProgramMethod) method)
                        .getMethodDeclaration();
            }

            return methodDeclaration instanceof ConstructorDeclaration
                    || methodDeclaration.getName().equals("<init>");
        });
    }

    @Override
    public ApplicabilityCondition visitIsFieldReference(
            IsFieldReferenceContext ctx) {
        return new ApplicabilityCondition(info -> {
            // This check may also be called for void methods, during the
            // selection of suitable translation. Therefore, locVarOrFieldRef
            // may occasionally be no present.
            Optional<Object> locVarOrFieldRef = info.getInstantiations()
                    .getInstantiationFor(ctx.LOC_REF().getText());

            return locVarOrFieldRef.isPresent()
                    ? (locVarOrFieldRef.get() instanceof FieldReference)
                    : false;
        });
    }

    @Override
    public ApplicabilityCondition visitIsStaticExpression(
            IsStaticExpressionContext ctx) {
        return new ApplicabilityCondition(info -> {
            ProgramMethod pm = (ProgramMethod) info.getInstantiations()
                    .getInstantiationFor(ctx.LOC_REF().getText()).get();
            return pm.isStatic();
        });
    }

    @Override
    public ApplicabilityCondition visitIsVoidExpression(
            IsVoidExpressionContext ctx) {
        return new ApplicabilityCondition(info -> {
            ProgramMethod pm = (ProgramMethod) info.getInstantiations()
                    .getInstantiationFor(ctx.LOC_REF().getText()).get();
            return pm.isVoid();
        });
    }

    @Override
    public ApplicabilityCondition visitIsResultVarExpression(
            IsResultVarExpressionContext ctx) {
        return new ApplicabilityCondition(info -> {
            // XXX This is a hack for ignoring result_* and self_* variables
            // introduced by Operation Contract rule applications. We should
            // actually check whether this variable was indeed introduced by
            // such an application...

            Expression expr = (Expression) info.getInstantiations()
                    .getInstantiationFor(ctx.LOC_REF().getText()).get();

            if (!(expr instanceof LocationVariable)) {
                return false;
            }

            LocationVariable locVar = (LocationVariable) expr;
            return locVar.name().toString().startsWith("result_")
                    || locVar.name().toString().startsWith("self");
        });
    }
    
    @Override
    public StringTranslationTacletASTElement visitGetUppermostLoopEntryLabel(
            GetUppermostLoopEntryLabelContext ctx) {
        return new StringTranslationTacletASTElement(UPPERMOST_LOOP_ENTRY_SPECIAL_LBL);
    }
    
    @Override
    public StringTranslationTacletASTElement visitGetUppermostLoopExitLabel(
            GetUppermostLoopExitLabelContext ctx) {
        return new StringTranslationTacletASTElement(UPPERMOST_LOOP_EXIT_SPECIAL_LBL);
    }
    
    @Override
    public TranslationTacletASTElement visitIsValidInStateExpression(
            IsValidInStateExpressionContext ctx) {
        // TODO Enter actual method body
        return super.visitIsValidInStateExpression(ctx);
    }

    @Override
    public ApplicabilityCondition visitSimple_arithmetic_expression(
            Simple_arithmetic_expressionContext ctx) {
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
        return new LabeledBytecodeInstr(
                getUniquePerTranslationLabelName(ctx.LABEL().getText()),
                (Instruction) visit(ctx.bytecode_instr()));
    }

    @Override
    public SuperCallInstruction visitSuper_call(Super_callContext ctx) {
        return new SuperCallInstruction(ctx.mname.getText(),
                ctx.elist.getText());
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
                ctx.loc_var_unary_instrs().getText(), ctx.LOC_REF() == null
                        ? ctx.integer().getText() : ctx.LOC_REF().getText());
    }

    @Override
    public LabelUnaryBytecodeInstr visitLabelUnaryBytecodeInstr(
            LabelUnaryBytecodeInstrContext ctx) {
        return new LabelUnaryBytecodeInstr(ctx.label_unary_instrs().getText(),
                getUniquePerTranslationLabelName(ctx.LABEL().getText()));
    }

    @Override
    public TranslationTacletASTElement visitSpecialLabelUnaryBytecodeInstr(
            SpecialLabelUnaryBytecodeInstrContext ctx) {
        return new LabelUnaryBytecodeInstr(ctx.label_unary_instrs().getText(),
                ((StringTranslationTacletASTElement) visit(
                        ctx.special_lbl_term())).getString());
    }

    @Override
    public IntegerUnaryBytecodeInstr visitIntUnaryBytecodeInstr(
            IntUnaryBytecodeInstrContext ctx) {
        return new IntegerUnaryBytecodeInstr(
                ctx.int_const_unary_instrs().getText(),
                Integer.parseInt(ctx.integer().getText()));
    }

    @Override
    public LdcInstr visitStringLitUnaryBytecodeInstr(
            StringLitUnaryBytecodeInstrContext ctx) {
        return new LdcInstr(ctx.LOC_REF().getText());
    }

    @Override
    public TypeInstr visitSpecialUnaryInstrs(SpecialUnaryInstrsContext ctx) {
        boolean isTypeLiteral = false;
        String arg = null;

        if (ctx.LOC_REF() != null) {
            isTypeLiteral = false;
            arg = ctx.LOC_REF().getText();
        } else if (ctx.type_spec() != null) {
            isTypeLiteral = true;
            arg = ctx.type_spec().getText();
        }

        return new TypeInstr(ctx.special_unary_instrs().getText(), arg,
                isTypeLiteral);
    }

    @Override
    public Instruction visitField_instr(Field_instrContext ctx) {
        return new FieldInstr(ctx.instr.getText(), ctx.field.getText());
    }

    @Override
    public LoadInstruction visitSimple_load_instr(
            Simple_load_instrContext ctx) {
        return new LoadInstruction(ctx.LOC_REF().getText(), false);
    }

    @Override
    public LoadInstruction visitNegated_load_instr(
            Negated_load_instrContext ctx) {
        return new LoadInstruction(ctx.LOC_REF().getText(), true);
    }

    @Override
    public ParamsLoadInstruction visitParams_load_instr(
            Params_load_instrContext ctx) {
        return new ParamsLoadInstruction(ctx.LOC_REF().getText());
    }

    @Override
    public StoreInstruction visitStore_instr(Store_instrContext ctx) {
        return new StoreInstruction(ctx.LOC_REF().getText());
    }

    @Override
    public InvokeInstr visitInvoke_instr_literal(
            Invoke_instr_literalContext ctx) {
        String op = ctx.invoke_op().getText();
        String cls = ctx.method_descriptor().typename.getText();
        String mname = ctx.method_descriptor().mname.getText();
        String sig = ctx.method_descriptor().sig.getText();

        return new InvokeInstr(op, cls, mname, sig);
    }

    @Override
    public InvokeInstr visitInvoke_instr_sv(Invoke_instr_svContext ctx) {
        return new InvokeInstr(ctx.invoke_op().getText(),
                ctx.LOC_REF().getText());
    }

    @Override
    public ChildCall visitChild_call(Child_callContext ctx) {
        return new ChildCall(Integer.parseInt(ctx.NUMBER().getText()));
    }

    @Override
    public LoopLabelInstruction visitPushLoopEntryLabel(
            PushLoopEntryLabelContext ctx) {
        return new LoopLabelInstruction(LoopLabelInstruction.LOOP_ENTRY,
                ctx.LABEL().getText());
    }

    @Override
    public LoopLabelInstruction visitPushLoopExitLabel(
            PushLoopExitLabelContext ctx) {
        return new LoopLabelInstruction(LoopLabelInstruction.LOOP_EXIT,
                ctx.LABEL().getText());
    }

    @Override
    public LoopLabelInstruction visitPopLoopEntryLabel(
            PopLoopEntryLabelContext ctx) {
        return new LoopLabelInstruction(LoopLabelInstruction.LOOP_ENTRY);
    }

    @Override
    public TranslationTacletASTElement visitPopLoopExitLabel(
            PopLoopExitLabelContext ctx) {
        return new LoopLabelInstruction(LoopLabelInstruction.LOOP_EXIT);
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
    private String getUniquePerTranslationLabelName(String labelName) {
        String result = null;

        if (labelMap.containsKey(labelName)) {
            result = labelMap.get(labelName);
        } else {
            result = "l" + labelCounter++;
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
        } else {
            return fileName;
        }
    }
}
