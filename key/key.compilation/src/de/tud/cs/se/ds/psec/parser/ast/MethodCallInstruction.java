package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.parser.exceptions.UnsupportedFeatureException;
import de.tud.cs.se.ds.psec.util.InformationExtraction;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.tud.cs.se.ds.psec.util.Utilities;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * A special bytecode {@link Instruction} for method calls. Comprises a
 * {@link SchemaVariable} reference to a {@link MethodBodyStatement}.
 *
 * @author Dominic Scheurer
 */
public class MethodCallInstruction extends Instruction {
    private static final Logger logger = LogManager.getFormatterLogger();
    String methodBodyStatementSV;

    /**
     * @param insn
     *            The bytecode instruction.
     */
    public MethodCallInstruction(String methodBodyStatementSV) {
        super();
        this.methodBodyStatementSV = methodBodyStatementSV;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, TacletApp app, Services services,
            List<TacletASTNode> children) {

        MethodBodyStatement mbs = (MethodBodyStatement) getTacletAppInstValue(
                app, methodBodyStatementSV);

        IProgramMethod pm = mbs.getProgramMethod(services);

        if (!pm.getName().equals("<init>")) {
            // XXX: Shouldn't be too hard to also support general method calls;
            // probably only have to replace INVOKESPECIAL by another opcode
            // depending on the situation.
            String msg = Utilities.format(
                    "Currently only supporting calls to constructors; problem: %s",
                    mbs);
            logger.error(msg);
            throw new UnsupportedFeatureException(msg);
        }

        if (!pm.isStatic()) {

            mv.visitVarInsn(ALOAD, 0);

            for (Expression expr : mbs.getArguments()) {
                loadExpressionToStack(mv, pvHelper, expr);
            }

            mv.visitMethodInsn(INVOKESPECIAL,
                    InformationExtraction.toInternalName(pm.getContainerType()),
                    pm.getName(),
                    InformationExtraction.getMethodTypeDescriptor(pm), false);

        } else {
            String msg = Utilities.format(
                    "Currently not supporting static method calls; problem: %s",
                    mbs);
            logger.error(msg);
            throw new UnsupportedFeatureException(msg);
        }

    }

}
