package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.Services.ITermProgramVariableCollectorFactory;
import de.uka.ilkd.key.java.recoderext.KeYCrossReferenceServiceConfiguration;
import de.uka.ilkd.key.logic.InnerVariableNamer;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;

public class JavaServices implements ProgramServices {
    /** used to convert types, expressions and so on to logic elements
     * (in special into to terms or formulas)
     */
    private TypeConverter typeconverter;
    /**
     * the information object on the Java model
     */
    private JavaInfo javainfo;
    /**
     * variable namer for inner renaming
     */
    private VariableNamer innerVarNamer;
    private JavaModel javaModel;
    private ITermProgramVariableCollectorFactory factory;

    /** used to determine whether an expression is a compile-time 
     * constant and if so the type and result of the expression
     */
    private ConstantExpressionEvaluator cee;


    public JavaServices(Services services) {
        this.innerVarNamer = new InnerVariableNamer(services);
        this.factory = new ITermProgramVariableCollectorFactory(){
            @Override
            public TermProgramVariableCollector create(Services p_services) {
               return new TermProgramVariableCollector(p_services);
            }};
        
        this.typeconverter = new TypeConverter(services);        
        this.javainfo = new JavaInfo(new KeYProgModelInfo(services, typeconverter, new KeYRecoderExcHandler()), services);

        this.cee = new ConstantExpressionEvaluator(services);
    }

    public JavaServices(Services services, KeYCrossReferenceServiceConfiguration crsc, KeYRecoderMapping rec2key) {
        this.innerVarNamer = new InnerVariableNamer(services);
        this.factory = new ITermProgramVariableCollectorFactory(){
            @Override
            public TermProgramVariableCollector create(Services p_services) {
               return new TermProgramVariableCollector(p_services);
            }};
        this.typeconverter = new TypeConverter(services);
        this.javainfo = new JavaInfo(new KeYProgModelInfo(services, crsc, rec2key, typeconverter), services);
        
        this.cee = new ConstantExpressionEvaluator(services);
    }


    public TypeConverter getTypeConverter() {
        return typeconverter;
    }

    public void setTypeconverter(TypeConverter typeconverter) {
        this.typeconverter = typeconverter;
    }

    public JavaInfo getJavaInfo() {
        return javainfo;
    }

    public void setJavainfo(JavaInfo javainfo) {
        this.javainfo = javainfo;
    }

    public VariableNamer getInnerVarNamer() {
        return innerVarNamer;
    }

    public void setInnerVarNamer(VariableNamer innerVarNamer) {
        this.innerVarNamer = innerVarNamer;
    }

    public JavaModel getJavaModel() {
        return javaModel;
    }

    public void setJavaModel(JavaModel javaModel) {
        assert this.getJavaModel() == null;
        this.javaModel = javaModel;
    }

    public ITermProgramVariableCollectorFactory getFactory() {
        return factory;
    }

    public void setFactory(ITermProgramVariableCollectorFactory factory) {
        this.factory = factory;
    }

    public ConstantExpressionEvaluator getConstantExpressionEvaluator() {
        return cee;
    }
}