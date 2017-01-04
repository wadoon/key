package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.GlobalLabelHelper;
import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.compiler.exceptions.UnexpectedTranslationSituationException;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.tud.cs.se.ds.psec.util.Utilities;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * An instruction to an Integer {@link ProgramVariable} or {@link Literal} onto
 * the stack.
 *
 * @author Dominic Scheurer
 */
public class ParamsLoadInstruction extends Instruction {
    private String schemaVar;

    /**
     * Constructs a {@link ParamsLoadInstruction} for loading the element
     * specified in the symbolic execution taclet by the schema variable
     * schemaVar onto the stack. If negative is set, then the element will be
     * negated.
     * 
     * @param schemaVar
     * @param negative
     */
    public ParamsLoadInstruction(String schemaVar) {
        this.schemaVar = schemaVar;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            GlobalLabelHelper globalLabelHelper, UniqueLabelManager labelManager,
            RuleInstantiations instantiations, Services services, List<TacletASTNode> children) {
        Iterable<?> params = (Iterable<?>) instantiations
                .getInstantiationFor(schemaVar).get();

        params.forEach(param -> {
            Expression e = null;

            if (param instanceof Term) {
                Term t = (Term) param;
                IntegerLDT integerLDT = services.getTypeConverter()
                        .getIntegerLDT();

                if (t.op() instanceof Expression) {
                    e = (Expression) t.op();
                } else if (t.op() instanceof Function && ((Function) t.op())
                        .equals(integerLDT.getNumberSymbol())) {
                    // This is a Z-Term
                    e = integerLDT.translateTerm(t, null, services);
                } else {
                    throwUnexpectedException(param);
                }
            } else if (param instanceof Expression) {
                e = (Expression) param;
            } else {
                throwUnexpectedException(param);
            }

            loadExpressionToStack(mv, pvHelper, e);
        });
    }

    private void throwUnexpectedException(Object param) {
        throw new UnexpectedTranslationSituationException(Utilities
                .format("Unexpected parameter type: %s", param.getClass()));
    }

}
