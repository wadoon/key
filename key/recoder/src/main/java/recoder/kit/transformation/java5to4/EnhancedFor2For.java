package recoder.kit.transformation.java5to4;

import recoder.CrossReferenceServiceConfiguration;
import recoder.NamedModelElement;
import recoder.ProgramFactory;
import recoder.abstraction.Type;
import recoder.abstraction.Variable;
import recoder.java.*;
import recoder.java.declaration.LocalVariableDeclaration;
import recoder.java.declaration.VariableSpecification;
import recoder.java.expression.operator.LessThan;
import recoder.java.reference.MethodReference;
import recoder.java.reference.ReferencePrefix;
import recoder.java.statement.EnhancedFor;
import recoder.java.statement.For;
import recoder.java.statement.LabeledStatement;
import recoder.kit.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

public final class EnhancedFor2For extends TwoPassTransformation {
    private final CrossReferenceServiceConfiguration sc;

    private final EnhancedFor enhancedFor;

    private String iteratorName;

    private String arrayReferenceName;

    private Type guardType;

    private Type iteratorType;

    public EnhancedFor2For(CrossReferenceServiceConfiguration sc, EnhancedFor enhancedFor, String iteratorName, String arrayReferenceName) {
        super(sc);
        this.sc = sc;
        this.enhancedFor = enhancedFor;
        this.iteratorName = iteratorName;
        this.arrayReferenceName = arrayReferenceName;
    }

    public EnhancedFor2For(CrossReferenceServiceConfiguration sc, EnhancedFor enhancedFor) {
        this(sc, enhancedFor, null, null);
    }

    public ProblemReport analyze() {
        if (this.iteratorName != null) {
            Variable v = this.sc.getSourceInfo().getVariable(this.iteratorName, this.enhancedFor.getASTParent());
            if (v != null)
                return setProblemReport(new NameConflict(v));
        } else {
            this.iteratorName = VariableKit.createValidVariableName(this.sc.getSourceInfo(), this.enhancedFor.getASTParent(), "i");
        }
        if (this.arrayReferenceName != null) {
            Variable v = this.sc.getSourceInfo().getVariable(this.arrayReferenceName, this.enhancedFor.getASTParent());
            if (v != null)
                return setProblemReport(new NameConflict(v));
        } else {
            this.arrayReferenceName = VariableKit.createValidVariableName(this.sc.getSourceInfo(), this.enhancedFor.getASTParent(), "a");
        }
        this.guardType = this.sc.getSourceInfo().getType(this.enhancedFor.getGuard());
        if (this.guardType instanceof recoder.abstraction.ClassType) {
            MethodReference mr = getProgramFactory().createMethodReference((ReferencePrefix) this.enhancedFor.getGuard(), getProgramFactory().createIdentifier("iterator"));
            mr.setExpressionContainer(this.enhancedFor);
            this.iteratorType = this.sc.getSourceInfo().getType(mr);
        } else if (this.guardType instanceof recoder.abstraction.ArrayType) {
            this.iteratorType = null;
        } else {
            throw new IllegalStateException("Broken Model");
        }
        return setProblemReport(EQUIVALENCE);
    }

    public void transform() {
        LocalVariableDeclaration localVariableDeclaration1;
        MethodReference methodReference;
        ASTList<Expression> update;
        For for_1;
        EnhancedFor enhancedFor;
        super.transform();
        ProgramFactory pf = getProgramFactory();
        LocalVariableDeclaration firstStmnt = ((LocalVariableDeclaration) this.enhancedFor.getInitializers().get(0)).deepClone();
        if (this.iteratorType == null) {
            localVariableDeclaration1 = pf.createLocalVariableDeclaration(null, TypeKit.createTypeReference(pf, "int"), pf.createIdentifier(this.iteratorName), pf.createIntLiteral(0));
            LessThan lessThan = pf.createLessThan(pf.createVariableReference(pf.createIdentifier(this.iteratorName)), pf.createArrayLengthReference(pf.createVariableReference(pf.createIdentifier(this.arrayReferenceName))));
            ASTArrayList aSTArrayList1 = new ASTArrayList(pf.createPostIncrement(pf.createVariableReference(pf.createIdentifier(this.iteratorName))));
            firstStmnt.getVariableSpecifications().get(0).setInitializer(pf.createArrayReference(pf.createVariableReference(pf.createIdentifier(this.arrayReferenceName)), new ASTArrayList(pf.createVariableReference(pf.createIdentifier(this.iteratorName)))));
        } else {
            localVariableDeclaration1 = pf.createLocalVariableDeclaration(null, TypeKit.createTypeReference(pf, this.iteratorType, true), pf.createIdentifier(this.iteratorName), pf.createMethodReference((ReferencePrefix) this.enhancedFor.getExpressionAt(0).deepClone(), pf.createIdentifier("iterator")));
            methodReference = pf.createMethodReference(pf.createVariableReference(pf.createIdentifier(this.iteratorName)), pf.createIdentifier("hasNext"));
            update = null;
            firstStmnt.getVariableSpecifications().get(0).setInitializer(pf.createMethodReference(pf.createVariableReference(pf.createIdentifier(this.iteratorName)), pf.createIdentifier("next")));
        }
        ASTArrayList aSTArrayList = new ASTArrayList(2);
        aSTArrayList.add(firstStmnt);
        if (this.enhancedFor.getStatementCount() > 0) {
            Statement s = this.enhancedFor.getStatementAt(0);
            if (s instanceof StatementBlock) {
                StatementBlock sb = (StatementBlock) s;
                for (int i = 0; i < sb.getStatementCount(); i++)
                    aSTArrayList.add(sb.getStatementAt(i).deepClone());
            } else {
                aSTArrayList.add(s.deepClone());
            }
        }
        For newFor = new For(new ASTArrayList(localVariableDeclaration1), methodReference, update, new StatementBlock(aSTArrayList));
        newFor.makeAllParentRolesValid();
        if (this.iteratorType == null) {
            LabeledStatement labeledStatement;
            ASTArrayList<Statement> sml = new ASTArrayList(2);
            LocalVariableDeclaration lvd = pf.createLocalVariableDeclaration(null, TypeKit.createTypeReference(pf, this.guardType), pf.createIdentifier(this.arrayReferenceName), this.enhancedFor.getGuard().deepClone());
            sml.add(lvd);
            For for_ = newFor;
            enhancedFor = this.enhancedFor;
            while (enhancedFor.getASTParent() instanceof LabeledStatement) {
                LabeledStatement labeledStatement1 = (LabeledStatement) enhancedFor.getASTParent();
                labeledStatement = new LabeledStatement(labeledStatement1.getIdentifier().deepClone(), for_);
            }
            sml.add(labeledStatement);
            StatementBlock statementBlock = pf.createStatementBlock(sml);
        } else {
            for_1 = newFor;
            enhancedFor = this.enhancedFor;
        }
        replace(enhancedFor, for_1);
    }
}
