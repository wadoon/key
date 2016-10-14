package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.compiler.exceptions.UnexpectedTranslationSituationException;
import de.tud.cs.se.ds.psec.util.InformationExtraction;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.tud.cs.se.ds.psec.util.Utilities;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.SchemaVariable;

/**
 * A special bytecode {@link Instruction} for method calls. Comprises a
 * {@link SchemaVariable} reference to a {@link ProgramMethod}.
 *
 * @author Dominic Scheurer
 */
public class MethodCallInstruction extends Instruction {
    private static final Logger logger = LogManager.getFormatterLogger();
    String programMethodSV;

    /**
     * @param programMethodSV
     *            The {@link SchemaVariable} for the {@link ProgramMethod} to
     *            execute.
     */
    public MethodCallInstruction(String programMethodSV) {
        this.programMethodSV = programMethodSV;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, RuleInstantiations instantiations,
            Services services, List<TacletASTNode> children) {

        Object method = instantiations.getInstantiationFor(programMethodSV)
                .get();
        IProgramMethod pm;

        if (method instanceof IProgramMethod) {
            pm = (IProgramMethod) method;
        } else {
            String msg = Utilities.format(
                    "Unexpected argument type for method call translation: %s",
                    method.getClass());
            logger.error(msg);
            throw new UnexpectedTranslationSituationException(msg);
        }

        boolean isConstructor = pm.getName().equals("<init>")
                || pm.isConstructor();

        IProgramMethod methodBeingCompiled = (IProgramMethod) instantiations
                .getInstantiationFor("#methodBeingCompiled").get();

        boolean isSuperMethod = !methodBeingCompiled.getContainerType()
                .getSort().equals(pm.getContainerType().getSort())
                && methodBeingCompiled.getContainerType().getSort()
                        .extendsTrans(pm.getContainerType().getSort());

        int opcode = INVOKEVIRTUAL;
        if (isConstructor || isSuperMethod) {
            opcode = INVOKESPECIAL;
        } else if (pm.isStatic()) {
            opcode = INVOKESTATIC;
        }

        // TODO Missing: INVOKEDYNAMIC, INVOKEINTERFACE

        String pmName = isConstructor ? "<init>" : pm.getName();

        mv.visitMethodInsn(opcode,
                InformationExtraction.toInternalName(pm.getContainerType()),
                pmName, InformationExtraction.getMethodTypeDescriptor(pm),
                false);

    }

}
