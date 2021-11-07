package de.uka.ilkd.key.java.transformations;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.TypeDeclaration;
import de.uka.ilkd.key.java.transformations.pipeline.*;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (11/7/21)
 */
public class KeyJavaPipeline {
    private final TransformationPipelineServices pipelineServices;
    private final List<JavaTransformer> steps = new LinkedList<>();

    public KeyJavaPipeline(TransformationPipelineServices pipelineServices) {
        this.pipelineServices = pipelineServices;
    }

    public static KeyJavaPipeline createDefault(TransformationPipelineServices pipelineServices) {
        KeyJavaPipeline p = new KeyJavaPipeline(pipelineServices);
        //new EnumClassBuilder(pipelineServices),
        p.add(new JMLTransformer(pipelineServices));
        p.add(new ImplicitFieldAdder(pipelineServices));
        p.add(new InstanceAllocationMethodBuilder(pipelineServices));
        p.add(new ConstructorNormalformBuilder(pipelineServices));
        p.add(new ClassPreparationMethodBuilder(pipelineServices));
        p.add(new ClassInitializeMethodBuilder(pipelineServices));
        p.add(new PrepareObjectBuilder(pipelineServices));
        p.add(new CreateBuilder(pipelineServices));
        p.add(new CreateObjectBuilder(pipelineServices));
        p.add(new LocalClassTransformation(pipelineServices));
        p.add(new ConstantStringExpressionEvaluator(pipelineServices));
        return p;
    }

    public void add(JavaTransformer step) {
        steps.add(step);
    }

    public void apply(Collection<CompilationUnit> compilationUnits) {
        for (CompilationUnit compilationUnit : compilationUnits) {
            for (TypeDeclaration<?> type : compilationUnit.getTypes()) {
                for (JavaTransformer step : steps) {
                    step.apply(type);
                }
            }
        }
    }
}
