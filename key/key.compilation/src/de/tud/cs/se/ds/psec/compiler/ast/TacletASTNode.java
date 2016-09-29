package de.tud.cs.se.ds.psec.compiler.ast;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.parser.ast.ApplicabilityCheckInput;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinition;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.operator.Negative;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Models a symbolic execution taclet and offers a method for translating it
 * into bytecode.
 *
 * @author Dominic Scheurer
 */
public class TacletASTNode implements Opcodes {
    private static final Logger logger = LogManager.getFormatterLogger();

    private List<TacletASTNode> children = new ArrayList<>();
    private MethodVisitor mv;
    private ProgVarHelper pvHelper;
    private TacletApp app;
    private List<TranslationDefinition> definitions;
    private String seTacletName;

    /**
     * Constructs a new {@link TacletASTNode} for a given {@link TacletApp}.
     * 
     * @param seTacletName
     *            The name of the SE taclet being translated.
     * @param definitions
     *            The {@link TranslationDefinition}s for the corresponding SE
     *            taclet.
     * @param mv
     *            The {@link MethodVisitor} for compiling the
     *            {@link TacletASTNode}.
     * @param pvHelper
     *            The {@link ProgVarHelper} of the corresponding method.
     * @param app
     *            The {@link TacletApp} to construct this {@link TacletASTNode}
     *            from.
     * 
     * @see TacletTranslationFactory
     */
    public TacletASTNode(String seTacletName,
            List<TranslationDefinition> definitions, MethodVisitor mv,
            ProgVarHelper pvHelper, TacletApp app) {
        this.app = app;
        this.mv = mv;
        this.pvHelper = pvHelper;
        this.definitions = definitions;
        this.seTacletName = seTacletName;
    }

    /**
     * Recursively translates this node and its children to bytecode.
     */
    public void compile() {
        logger.trace("Compiling %s", seTacletName);
        
        ApplicabilityCheckInput applCheckInput = new ApplicabilityCheckInput(
                children.size());

        List<TranslationDefinition> candidates = definitions.stream()
                .filter(d -> d.isApplicable(applCheckInput))
                .collect(Collectors.toList());

        if (candidates.size() < 1) {
            logger.error("No suitable translation found for the situation %s",
                    applCheckInput);
            System.exit(1);
        }
        else if (candidates.size() > 1) {
            logger.error(
                    "Too many translations (%s) found for the situation %s",
                    candidates.size(), applCheckInput);
            System.exit(1);
        }

        candidates.get(0).translate(mv, pvHelper, app, children);
    }

    /**
     * @return The {@link MethodVisitor} for compiling this
     *         {@link TacletASTNode} to bytecode.
     */
    protected MethodVisitor mv() {
        return mv;
    }

    /**
     * @return The {@link ProgVarHelper} of the corresponding method.
     */
    protected ProgVarHelper pvHelper() {
        return pvHelper;
    }

    /**
     * @return The {@link TacletApp} for this {@link TacletASTNode}.
     */
    protected TacletApp app() {
        return app;
    }

    /**
     * @return The children of this {@link TacletASTNode}.
     */
    public List<TacletASTNode> children() {
        return children;
    }

    /**
     * Adds a child to this {@link TacletASTNode}.
     * 
     * @param child
     *            The {@link TacletASTNode} to add as a child to the current
     *            one.
     */
    public void addChild(TacletASTNode child) {
        children.add(child);
    }

    /**
     * @return The name of the symbolic execution taclet that is represented by
     *         this {@link TacletASTNode}.
     */
    public String seTacletName() {
        return seTacletName;
    }

    /**
     * Recursively compiles the first child of this AST node.
     */
    protected void compileFirstChild() {
        if (!children.isEmpty()) {
            children.get(0).compile();
        }
    }

    /**
     * Loads the supplied IntLiteral or (Integer) LocationVariable onto the
     * stack.
     *
     * @param expr
     *            The expression to load onto the stack.
     */
    private void loadIntVarOrConst(Expression expr) {
        loadIntVarOrConst(expr, false);
    }

    /**
     * Loads the supplied {@link IntLiteral} or (Integer)
     * {@link LocationVariable} onto the stack.
     *
     * @param expr
     *            The expression to load onto the stack.
     * @param negative
     *            Set to true iff the given expression should be negated.
     */
    private void loadIntVarOrConst(Expression expr, boolean negative) {
        if (expr instanceof IntLiteral) {
            intConstInstruction((negative ? -1 : 1)
                    * Integer.parseInt(((IntLiteral) expr).toString()));
        }
        else if (expr instanceof LocationVariable) {
            mv.visitVarInsn(ILOAD, pvHelper.progVarNr((LocationVariable) expr));
        }
        else if (expr instanceof Negative) {
            loadIntVarOrConst((Expression) ((Negative) expr).getChildAt(0),
                    true);
        }
        else {
            logger.error(
                    "Currently not supporting the type %s in assignments, returns etc.",
                    expr.getClass());
            System.exit(1);
        }
    }

    /**
     * Loads the supplied {@link BooleanLiteral} or (boolean)
     * {@link LocationVariable} onto the stack.
     *
     * @param expr
     *            The expression to load onto the stack.
     */
    private void loadBooleanVarOrConst(Expression expr) {
        if (expr instanceof BooleanLiteral) {
            if (expr.toString().equals("true")) {
                mv.visitInsn(ICONST_1);
            }
            else {
                mv.visitInsn(ICONST_0);
            }
        }
        else if (expr instanceof LocationVariable) {
            mv.visitVarInsn(ILOAD, pvHelper.progVarNr((LocationVariable) expr));
        }
        else {
            logger.error(
                    "Currently not supporting the type %s in assignments, returns etc.",
                    expr.getClass());
            System.exit(1);
        }
    }

    /**
     * Displays an error expressing that only the types in
     * <code>acceptedTypesString</code> are expected, but <code>typeGiven</code>
     * is actually supplied.
     * 
     * @param acceptedTypesString
     *            A summary of the accepted types.
     * @param typeGiven
     *            The actually given type.
     */
    private void unsupportedTypeError(String acceptedTypesString,
            KeYJavaType typeGiven) {
        logger.error(
                "Only %s types considered so far, given: %s, translation %s",
                acceptedTypesString, typeGiven, getClass().getSimpleName());
        System.exit(1);
    }

    /**
     * Returns the value instantiated for the {@link SchemaVariable}
     * <code>sv</code> in the {@link TacletApp} for this {@link TacletASTNode}.
     *
     * @param sv
     *            The name of the {@link SchemaVariable} in the {@link Taclet}.
     * @return The instantiation for <code>sv</code>.
     */
    private Object getTacletAppInstValue(String sv) {
        return app.instantiations()
                .lookupValue(new de.uka.ilkd.key.logic.Name(sv));
    }

    /**
     * Writes a bytecode instruction to load the given integer constant.
     *
     * @param theInt
     *            The integer to load on the stack.
     */
    private void intConstInstruction(int theInt) {
        if (theInt < -1 || theInt > 5) {
            if (theInt >= Byte.MIN_VALUE && theInt <= Byte.MAX_VALUE) {
                mv.visitIntInsn(BIPUSH, theInt);
            }
            else if (theInt >= Short.MIN_VALUE && theInt <= Short.MAX_VALUE) {
                mv.visitIntInsn(SIPUSH, theInt);
            }
            else {
                logger.error(
                        "Constants in full Integer range not yet covered, given: %s",
                        theInt);
                System.exit(1);
            }
        }
        else if (theInt == -1) {
            mv.visitInsn(ICONST_M1);
        }
        else if (theInt == 0) {
            mv.visitInsn(ICONST_0);
        }
        else if (theInt == 1) {
            mv.visitInsn(ICONST_1);
        }
        else if (theInt == 2) {
            mv.visitInsn(ICONST_2);
        }
        else if (theInt == 3) {
            mv.visitInsn(ICONST_3);
        }
        else if (theInt == 4) {
            mv.visitInsn(ICONST_4);
        }
        else if (theInt == 5) {
            mv.visitInsn(ICONST_5);
        }
    }

}
