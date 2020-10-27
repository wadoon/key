package recoder.kit;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.io.SourceFileRepository;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.expression.ArrayInitializer;
import recoder.java.expression.ExpressionStatement;
import recoder.java.expression.Operator;
import recoder.java.expression.operator.*;
import recoder.java.reference.*;
import recoder.java.statement.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.*;

public abstract class Transformation {
    public static final NoProblem NO_PROBLEM = new NoProblem();
    public static final Equivalence EQUIVALENCE = new Equivalence();
    public static final Identity IDENTITY = new Identity();
    private CrossReferenceServiceConfiguration serviceConfiguration;
    private ProblemReport report;

    protected Transformation() {
    }

    public Transformation(CrossReferenceServiceConfiguration sc) {
        setServiceConfiguration(sc);
    }

    public static void doReplace(ProgramElement child, ProgramElement replacement) {
        if (child == replacement)
            return;
        NonTerminalProgramElement parent = child.getASTParent();
        if (parent != null)
            parent.replaceChild(child, replacement);
    }

    public static void doDetach(ProgramElement root) {
        NonTerminalProgramElement parent = root.getASTParent();
        if (parent != null)
            parent.replaceChild(root, null);
    }

    public static void doAttach(Identifier child, NamedProgramElement parent) {
        parent.setIdentifier(child);
        child.setParent(parent);
    }

    public static void doAttach(Import child, CompilationUnit parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<Import> list = parent.getImports();
        if (list == null)
            parent.setImports(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setParent(parent);
    }

    public static void doAttach(PackageSpecification child, CompilationUnit parent) {
        parent.setPackageSpecification(child);
        child.setParent(parent);
    }

    public static void doAttach(Statement child, StatementBlock parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<Statement> list = parent.getBody();
        if (list == null)
            parent.setBody(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setStatementContainer(parent);
    }

    public static void doAttach(StatementBlock child, MethodDeclaration parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    public static void doAttach(StatementBlock child, ClassInitializer parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    public static void doAttach(Statement child, Case parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<Statement> list = parent.getBody();
        if (list == null)
            parent.setBody(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setStatementContainer(parent);
    }

    public static void doAttach(Statement child, Default parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<Statement> list = parent.getBody();
        if (list == null)
            parent.setBody(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setStatementContainer(parent);
    }

    public static void doAttach(StatementBlock child, Catch parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    public static void doAttach(StatementBlock child, Finally parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    public static void doAttach(StatementBlock child, Try parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    public static void doAttach(Statement child, Then parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    public static void doAttach(Statement child, Else parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    public static void doAttach(StatementBlock child, LoopStatement parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    public static void doAttach(Statement child, LabeledStatement parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    public static void doAttach(StatementBlock child, SynchronizedBlock parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    public static void doAttach(TypeDeclaration child, CompilationUnit parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<TypeDeclaration> list = parent.getDeclarations();
        if (list == null)
            parent.setDeclarations(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setParent(parent);
    }

    public static void doAttach(ClassDeclaration child, StatementBlock parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<Statement> list = parent.getBody();
        if (list == null)
            parent.setBody(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setParent(parent);
    }

    public static void doAttach(ClassDeclaration child, New parent) {
        parent.setClassDeclaration(child);
        child.setParent(parent);
    }

    public static void doAttach(MemberDeclaration child, TypeDeclaration parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<MemberDeclaration> list = parent.getMembers();
        if (list == null)
            parent.setMembers(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setMemberParent(parent);
    }

    public static void doAttach(ParameterDeclaration child, MethodDeclaration parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<ParameterDeclaration> list = parent.getParameters();
        if (list == null)
            parent.setParameters(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setParameterContainer(parent);
    }

    public static void doAttach(ParameterDeclaration child, Catch parent) {
        parent.setParameterDeclaration(child);
        child.setParameterContainer(parent);
    }

    public static void doAttach(DeclarationSpecifier child, Declaration parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<DeclarationSpecifier> list = parent.getDeclarationSpecifiers();
        if (list == null)
            parent.setDeclarationSpecifiers(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setParent(parent);
    }

    public static void doAttach(Throws child, MethodDeclaration parent) {
        parent.setThrown(child);
        child.setParent(parent);
    }

    public static void doAttach(Implements child, ClassDeclaration parent) {
        parent.setImplementedTypes(child);
        child.setParent(parent);
    }

    public static void doAttach(Extends child, ClassDeclaration parent) {
        parent.setExtendedTypes(child);
        child.setParent(parent);
    }

    public static void doAttach(Extends child, InterfaceDeclaration parent) {
        parent.setExtendedTypes(child);
        child.setParent(parent);
    }

    public static void doAttach(FieldSpecification child, FieldDeclaration parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<FieldSpecification> list = parent.getFieldSpecifications();
        if (list == null)
            parent.setFieldSpecifications(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setParent(parent);
    }

    public static void doAttach(VariableSpecification child, LocalVariableDeclaration parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<VariableSpecification> list = parent.getVariableSpecifications();
        if (list == null)
            parent.setVariableSpecifications(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setParent(parent);
    }

    public static void doAttach(VariableSpecification child, ParameterDeclaration parent) {
        parent.setVariableSpecification(child);
        child.setParent(parent);
    }

    public static void doAttachAsBody(Statement child, LoopStatement parent) {
        parent.setBody(child);
        child.setStatementContainer(parent);
    }

    public static void doAttachAsInitializer(LoopInitializer child, For parent) {
        ASTArrayList aSTArrayList;
        ASTList<LoopInitializer> list = parent.getInitializers();
        if (list == null)
            parent.setInitializers(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(0, child);
        child.setStatementContainer(parent);
    }

    public static void doAttachAsCondition(Expression child, Assert parent) {
        parent.setCondition(child);
        child.setExpressionContainer(parent);
    }

    public static void doAttachAsMessage(Expression child, Assert parent) {
        parent.setMessage(child);
        child.setExpressionContainer(parent);
    }

    public static void doAttachAsGuard(Expression child, LoopStatement parent) {
        parent.setGuard(child);
        child.setExpressionContainer(parent);
    }

    public static void doAttachAsUpdate(ExpressionStatement child, For parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<Expression> list = parent.getUpdates();
        if (list == null)
            parent.setUpdates(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setExpressionContainer(parent);
    }

    public static void doAttach(Then child, If parent) {
        parent.setThen(child);
        child.setParent(parent);
    }

    public static void doAttach(Else child, If parent) {
        parent.setElse(child);
        child.setParent(parent);
    }

    public static void doAttach(Catch child, Try parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<Branch> list = parent.getBranchList();
        if (list == null)
            parent.setBranchList(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setParent(parent);
    }

    public static void doAttach(Finally child, Try parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<Branch> list = parent.getBranchList();
        if (list == null)
            parent.setBranchList(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setParent(parent);
    }

    public static void doAttach(Case child, Switch parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<Branch> list = parent.getBranchList();
        if (list == null)
            parent.setBranchList(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setParent(parent);
    }

    public static void doAttach(Default child, Switch parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<Branch> list = parent.getBranchList();
        if (list == null)
            parent.setBranchList(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setParent(parent);
    }

    public static void doAttach(ReferencePrefix child, ArrayLengthReference parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    public static void doAttachAsPrefix(ReferencePrefix child, ArrayReference parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    public static void doAttachAsArgument(Expression child, ArrayReference parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<Expression> list = parent.getDimensionExpressions();
        if (list == null)
            parent.setDimensionExpressions(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setExpressionContainer(parent);
    }

    public static void doAttach(ReferencePrefix child, FieldReference parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    public static void doAttachAsPrefix(TypeReference child, MetaClassReference parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    public static void doAttachAsPrefix(ReferencePrefix child, MethodReference parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    public static void doAttachAsArgument(Expression child, MethodReference parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<Expression> list = parent.getArguments();
        if (list == null)
            parent.setArguments(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setExpressionContainer(parent);
    }

    public static void doAttach(PackageReference child, PackageReference parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    public static void doAttach(ReferencePrefix child, SuperReference parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    public static void doAttach(TypeReference child, ThisReference parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    public static void doAttach(ReferencePrefix child, TypeReference parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    public static void doAttach(ReferencePrefix child, UncollatedReferenceQualifier parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    public static void doAttach(ArrayInitializer child, NewArray parent) {
        parent.setArrayInitializer(child);
        child.setExpressionContainer(parent);
    }

    public static void doAttach(ArrayInitializer child, ArrayInitializer parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<Expression> list = parent.getArguments();
        if (list == null)
            parent.setArguments(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setExpressionContainer(parent);
    }

    public static void doAttach(Expression child, VariableSpecification parent) {
        parent.setInitializer(child);
        child.setExpressionContainer(parent);
    }

    public static void doAttach(Expression child, ExpressionJumpStatement parent) {
        parent.setExpression(child);
        child.setExpressionContainer(parent);
    }

    public static void doAttach(Expression child, If parent) {
        parent.setExpression(child);
        child.setExpressionContainer(parent);
    }

    public static void doAttach(Expression child, Switch parent) {
        parent.setExpression(child);
        child.setExpressionContainer(parent);
    }

    public static void doAttachAsLabel(Expression child, Case parent) {
        parent.setExpression(child);
        child.setExpressionContainer(parent);
    }

    public static void doAttachAsPrefix(ReferencePrefix child, New parent) {
        parent.setReferencePrefix(child);
        child.setReferenceSuffix(parent);
    }

    public static void doAttachAsArgument(Expression child, Operator parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<Expression> list = parent.getArguments();
        if (list == null)
            parent.setArguments(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setExpressionContainer(parent);
    }

    public static void doAttachAsArgument(Expression child, SpecialConstructorReference parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<Expression> list = parent.getArguments();
        if (list == null)
            parent.setArguments(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setExpressionContainer(parent);
    }

    public static void doAttachAsArgument(TypeReference child, TypeOperator parent) {
        parent.setTypeReference(child);
        child.setParent(parent);
    }

    public static void doAttachAsArgument(Expression child, TypeCast parent) {
        ASTArrayList aSTArrayList;
        ASTList<Expression> list = parent.getArguments();
        if (list == null)
            parent.setArguments(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(0, child);
        child.setExpressionContainer(parent);
    }

    public static void doAttachAsArgument(Expression child, Instanceof parent) {
        ASTArrayList aSTArrayList;
        ASTList<Expression> list = parent.getArguments();
        if (list == null)
            parent.setArguments(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(0, child);
        child.setExpressionContainer(parent);
    }

    public static void doAttachAsArgument(Expression child, New parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<Expression> list = parent.getArguments();
        if (list == null)
            parent.setArguments(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setExpressionContainer(parent);
    }

    public static void doAttachAsArgument(Expression child, NewArray parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<Expression> list = parent.getArguments();
        if (list == null)
            parent.setArguments(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setExpressionContainer(parent);
    }

    public static void doAttach(TypeReference child, Import parent) {
        parent.setReference(child);
        child.setParent(parent);
    }

    public static void doAttach(PackageReference child, Import parent) {
        parent.setReference(child);
        child.setParent(parent);
    }

    public static void doAttach(PackageReference child, PackageSpecification parent) {
        parent.setPackageReference(child);
        child.setParent(parent);
    }

    public static void doAttach(TypeReference child, InheritanceSpecification parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<TypeReference> list = parent.getSupertypes();
        if (list == null)
            parent.setSupertypes(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setParent(parent);
    }

    public static void doAttach(TypeReference child, MethodDeclaration parent) {
        parent.setTypeReference(child);
        child.setParent(parent);
    }

    public static void doAttach(TypeReference child, VariableDeclaration parent) {
        parent.setTypeReference(child);
        child.setParent(parent);
    }

    public static void doAttach(TypeReference child, Throws parent, int index) {
        ASTArrayList aSTArrayList;
        ASTList<TypeReference> list = parent.getExceptions();
        if (list == null)
            parent.setExceptions(aSTArrayList = new ASTArrayList());
        aSTArrayList.add(index, child);
        child.setParent(parent);
    }

    public CrossReferenceServiceConfiguration getServiceConfiguration() {
        return this.serviceConfiguration;
    }

    public void setServiceConfiguration(CrossReferenceServiceConfiguration sc) {
        if (sc == null)
            throw new IllegalArgumentException("A transformation needs a service configuration to work");
        this.serviceConfiguration = sc;
    }

    public boolean isVisible() {
        return true;
    }

    protected ProgramFactory getProgramFactory() {
        return this.serviceConfiguration.getProgramFactory();
    }

    protected ChangeHistory getChangeHistory() {
        return this.serviceConfiguration.getChangeHistory();
    }

    protected SourceInfo getSourceInfo() {
        return this.serviceConfiguration.getSourceInfo();
    }

    protected CrossReferenceSourceInfo getCrossReferenceSourceInfo() {
        return this.serviceConfiguration.getCrossReferenceSourceInfo();
    }

    protected NameInfo getNameInfo() {
        return this.serviceConfiguration.getNameInfo();
    }

    protected SourceFileRepository getSourceFileRepository() {
        return this.serviceConfiguration.getSourceFileRepository();
    }

    public ProblemReport execute() {
        return setProblemReport(IDENTITY);
    }

    public ProblemReport getProblemReport() {
        return this.report;
    }

    protected ProblemReport setProblemReport(ProblemReport report) {
        return this.report = report;
    }

    public void rollback() throws NoSuchTransformationException {
        if (isVisible())
            getChangeHistory().rollback(this);
    }

    public String toString() {
        String result = getClass().getName();
        int ldp = result.lastIndexOf('.');
        if (ldp > 0)
            result = result.substring(ldp + 1);
        return result;
    }

    protected final void replace(ProgramElement child, ProgramElement replacement) {
        if (child == replacement)
            return;
        NonTerminalProgramElement parent = child.getASTParent();
        if (parent != null)
            parent.replaceChild(child, replacement);
        if (isVisible())
            getChangeHistory().replaced(child, replacement);
    }

    protected final void detach(ProgramElement root) {
        int position;
        NonTerminalProgramElement parent = root.getASTParent();
        if (parent != null) {
            position = parent.getChildPositionCode(root);
            parent.replaceChild(root, null);
        } else {
            position = 0;
        }
        if (isVisible())
            getChangeHistory().detached(root, position);
    }

    protected final void attach(CompilationUnit child) {
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Identifier child, NamedProgramElement parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Import child, CompilationUnit parent, int index) {
        doAttach(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(PackageSpecification child, CompilationUnit parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Statement child, StatementBlock parent, int index) {
        doAttach(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(StatementBlock child, MethodDeclaration parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(StatementBlock child, ClassInitializer parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Statement child, Case parent, int index) {
        doAttach(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Statement child, Default parent, int index) {
        doAttach(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(StatementBlock child, Catch parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(StatementBlock child, Finally parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(StatementBlock child, Try parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Statement child, Then parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Statement child, Else parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(StatementBlock child, LoopStatement parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Statement child, LabeledStatement parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(StatementBlock child, SynchronizedBlock parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(TypeDeclaration child, CompilationUnit parent, int index) {
        doAttach(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(ClassDeclaration child, StatementBlock parent, int index) {
        doAttach(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(ClassDeclaration child, New parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(MemberDeclaration child, TypeDeclaration parent, int index) {
        doAttach(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(ParameterDeclaration child, MethodDeclaration parent, int index) {
        doAttach(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(ParameterDeclaration child, Catch parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Modifier child, Declaration parent, int index) {
        doAttach(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Throws child, MethodDeclaration parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Implements child, ClassDeclaration parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Extends child, ClassDeclaration parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Extends child, InterfaceDeclaration parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(FieldSpecification child, FieldDeclaration parent, int index) {
        doAttach(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(VariableSpecification child, LocalVariableDeclaration parent, int index) {
        doAttach(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(VariableSpecification child, ParameterDeclaration parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attachAsBody(Statement child, LoopStatement parent) {
        doAttachAsBody(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attachAsInitializer(LoopInitializer child, For parent) {
        doAttachAsInitializer(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attachAsGuard(Expression child, LoopStatement parent) {
        doAttachAsGuard(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attachAsUpdate(ExpressionStatement child, For parent, int index) {
        doAttachAsUpdate(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attachAsCondition(Expression child, Assert parent) {
        doAttachAsCondition(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attachAsMessage(Expression child, Assert parent) {
        doAttachAsMessage(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Then child, If parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Else child, If parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Catch child, Try parent, int index) {
        doAttach(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Finally child, Try parent, int index) {
        doAttach(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Case child, Switch parent, int index) {
        doAttach(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Default child, Switch parent, int index) {
        doAttach(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(ReferencePrefix child, ArrayLengthReference parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attachAsPrefix(ReferencePrefix child, ArrayReference parent) {
        doAttachAsPrefix(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attachAsArgument(Expression child, ArrayReference parent, int index) {
        doAttachAsArgument(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(ReferencePrefix child, FieldReference parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attachAsPrefix(TypeReference child, MetaClassReference parent) {
        doAttachAsPrefix(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attachAsPrefix(ReferencePrefix child, MethodReference parent) {
        doAttachAsPrefix(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attachAsArgument(Expression child, MethodReference parent, int index) {
        doAttachAsArgument(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(PackageReference child, PackageReference parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(ReferencePrefix child, SuperReference parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(TypeReference child, ThisReference parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(ReferencePrefix child, TypeReference parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(ReferencePrefix child, UncollatedReferenceQualifier parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(ArrayInitializer child, NewArray parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(ArrayInitializer child, ArrayInitializer parent, int index) {
        doAttach(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Expression child, VariableSpecification parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Expression child, ExpressionJumpStatement parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Expression child, If parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attach(Expression child, Switch parent) {
        doAttach(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attachAsLabel(Expression child, Case parent) {
        doAttachAsLabel(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attachAsPrefix(ReferencePrefix child, New parent) {
        doAttachAsPrefix(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attachAsArgument(Expression child, Operator parent, int index) {
        doAttachAsArgument(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attachAsArgument(Expression child, SpecialConstructorReference parent, int index) {
        doAttachAsArgument(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attachAsArgument(TypeReference child, TypeOperator parent) {
        doAttachAsArgument(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attachAsArgument(Expression child, TypeCast parent) {
        doAttachAsArgument(child, parent);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attachAsArgument(Expression child, New parent, int index) {
        doAttachAsArgument(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }

    protected final void attachAsArgument(Expression child, NewArray parent, int index) {
        doAttachAsArgument(child, parent, index);
        if (isVisible())
            getChangeHistory().attached(child);
    }
}
