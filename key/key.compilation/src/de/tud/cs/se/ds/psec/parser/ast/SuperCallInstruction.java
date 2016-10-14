package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableArray;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.compiler.exceptions.UnexpectedTranslationSituationException;
import de.tud.cs.se.ds.psec.util.InformationExtraction;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.tud.cs.se.ds.psec.util.Utilities;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.SchemaVariable;

/**
 * A special bytecode {@link Instruction} for super calls.
 *
 * @author Dominic Scheurer
 */
public class SuperCallInstruction extends Instruction {
    String methodNameSV;
    String argListSV;

    /**
     * @param methodNameSV
     *            The {@link SchemaVariable} instantiated with the method name
     *            to be called
     * @param argListSV
     *            The {@link SchemaVariable} instantiated with the list of
     *            arguments
     */
    public SuperCallInstruction(String methodNameSV, String argListSV) {
        this.methodNameSV = methodNameSV;
        this.argListSV = argListSV;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, RuleInstantiations instantiations,
            Services services, List<TacletASTNode> children) {

        MethodName methodName = (MethodName) instantiations
                .getInstantiationFor(methodNameSV).get();
        @SuppressWarnings("unchecked")
        ImmutableArray<Expression> args = (ImmutableArray<Expression>) instantiations
                .getInstantiationFor("#selist").get();

        ExecutionContext executionContext = (ExecutionContext) instantiations
                .getInstantiationFor("#ex").get();

        KeYJavaType superType = services.getJavaInfo().getSuperclass(
                executionContext.getTypeReference().getKeYJavaType());

        List<ProgramMethod> suitableMethods = Utilities
                .toStream(((ClassDeclaration) superType.getJavaType())
                        .getMembers())
                .filter(memberDecl -> (memberDecl instanceof ProgramMethod))
                .map(m -> (ProgramMethod) m)
                .filter(mDecl -> mDecl.getName().equals(methodName.toString()))
                .filter(mDecl -> {
                    if (args.size() != mDecl.getParameters().size()) {
                        return false;
                    }

                    for (int i = 0; i < mDecl.getParameters().size(); i++) {
                        KeYJavaType calledArgType = args.get(i)
                                .getKeYJavaType(services, executionContext);
                        KeYJavaType declArgType = mDecl.getParameterType(i);
                        if (!calledArgType.getSort()
                                .extendsTrans(declArgType.getSort())) {
                            return false;
                        }
                    }

                    return true;
                }).collect(Collectors.toList());

        if (suitableMethods.size() != 1) {
            throw new UnexpectedTranslationSituationException(Utilities.format(
                    "Wrong number of matching methods for %s, expected: 1, actual: %s",
                    methodName.toString(), suitableMethods.size()));
        }

        ProgramMethod pm = suitableMethods.get(0);

        // TODO check if we got all the right opcodes...
        mv.visitMethodInsn(
                pm.isConstructor() || pm.getName().equals("<init>")
                        ? INVOKESPECIAL : INVOKEVIRTUAL,
                InformationExtraction.toInternalName(pm.getContainerType()),
                pm.getName(), InformationExtraction.getMethodTypeDescriptor(pm),
                false);

    }

}
