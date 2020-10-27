package recoder.kit.transformation;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.abstraction.Type;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.expression.operator.CopyAssignment;
import recoder.java.reference.TypeReference;
import recoder.java.reference.VariableReference;
import recoder.kit.*;
import recoder.list.generic.ASTList;
import recoder.service.SourceInfo;
import recoder.util.Debug;

import java.util.ArrayList;
import java.util.List;

public class ShiftPreceedingStatementExpressions extends TwoPassTransformation {
    private final Expression expression;

    private List<Expression> preceeding;

    private List<Statement> tempVarDecls;

    private List<VariableReference> tempVarRefs;

    private NonTerminalProgramElement parent;

    private PrepareStatementList preparer;

    private Statement newParent;

    public ShiftPreceedingStatementExpressions(CrossReferenceServiceConfiguration sc, Expression x) {
        super(sc);
        if (x == null)
            throw new IllegalArgumentException("Missing expression");
        this.expression = x;
    }

    public ProblemReport analyze() {
        this.preceeding = ExpressionKit.collectPreceedingExpressions(this.expression);
        int exSize = this.preceeding.size();
        for (int i = exSize - 1; i >= 0; i--) {
            if (!ExpressionKit.containsStatements(this.preceeding.get(i)))
                this.preceeding.remove(i);
        }
        if (this.expression instanceof Statement && ((Statement) this.expression).getStatementContainer() != null) {
            this.parent = (NonTerminalProgramElement) this.expression;
        } else {
            for (Expression expression = this.expression; expression != null; nonTerminalProgramElement = this.parent) {
                NonTerminalProgramElement nonTerminalProgramElement;
                this.parent = expression.getASTParent();
                if (this.parent instanceof Statement && (
                        (Statement) this.parent).getStatementContainer() != null)
                    break;
                if (this.parent instanceof FieldSpecification)
                    break;
            }
        }
        exSize = this.preceeding.size();
        if (exSize == 0 && this.parent instanceof Statement)
            return setProblemReport(IDENTITY);
        ProgramFactory f = getProgramFactory();
        SourceInfo si = getSourceInfo();
        if (exSize > 0) {
            Type[] exTypes = new Type[exSize];
            for (int j = 0; j < exSize; j++) {
                Expression ex = this.preceeding.get(j);
                exTypes[j] = si.getType(ex);
            }
            String[] varNames = VariableKit.getNewVariableNames(si, exTypes, this.expression);
            this.tempVarDecls = new ArrayList<Statement>(exSize);
            this.tempVarRefs = new ArrayList<VariableReference>(exSize);
            for (int k = 0; k < exSize; k++) {
                Type t = exTypes[k];
                TypeReference minTypeRef = TypeKit.createTypeReference(si, t, this.expression);
                String varName = varNames[k];
                LocalVariableDeclaration vdecl = f.createLocalVariableDeclaration(minTypeRef, f.createIdentifier(varName));
                VariableSpecification vspec = vdecl.getVariables().get(0);
                doAttach(this.preceeding.get(k).deepClone(), vspec);
                this.tempVarDecls.add(vdecl);
                VariableReference vref = f.createVariableReference(f.createIdentifier(varName));
                vref.makeAllParentRolesValid();
                this.tempVarRefs.add(vref);
            }
        }
        if (this.parent instanceof Statement) {
            this.preparer = new PrepareStatementList(getServiceConfiguration(), (Statement) this.parent, isVisible());
            ProblemReport report = this.preparer.analyze();
            if (report instanceof recoder.kit.Problem)
                return setProblemReport(report);
        }
        return setProblemReport(EQUIVALENCE);
    }

    public void transform() {
        super.transform();
        if (this.parent instanceof Statement)
            this.newParent = (Statement) this.parent;
        int exSize = this.preceeding.size();
        if (exSize == 0)
            return;
        int tempSize = this.tempVarDecls.size();
        if (this.parent instanceof Statement) {
            this.preparer.transform();
            ASTList<Statement> aSTList = this.preparer.getStatementList();
            this.parent = (NonTerminalProgramElement) this.preparer.getStatement();
            int destIndex;
            for (destIndex = 0; aSTList.get(destIndex) != this.parent; destIndex++) ;
            int i;
            for (i = 0; i < tempSize; i++) {
                Statement child = this.tempVarDecls.get(i);
                aSTList.add(destIndex, child);
                child.setStatementContainer(((Statement) this.parent).getStatementContainer());
                if (isVisible())
                    getChangeHistory().attached(child);
            }
            for (i = 0; i < exSize; i++)
                replace(this.preceeding.get(i), this.tempVarRefs.get(i));
        } else if (this.parent instanceof FieldSpecification) {
            ProgramFactory f = getProgramFactory();
            FieldSpecification fs = (FieldSpecification) this.parent;
            StatementBlock body = f.createStatementBlock();
            for (int i = 0; i < tempSize; i++)
                doAttach(this.tempVarDecls.get(i), body, i);
            Expression init = fs.getInitializer();
            Debug.assertNonnull(init);
            for (int j = 0; j < exSize; j++)
                replace(this.preceeding.get(j), this.tempVarRefs.get(j));
            detach(init);
            CopyAssignment ca = f.createCopyAssignment(f.createVariableReference(f.createIdentifier(fs.getName())), init.deepClone());
            this.newParent = ca;
            doAttach(ca, body, tempSize);
            FieldDeclaration fd = (FieldDeclaration) fs.getParent();
            ClassInitializer ci = fd.isStatic() ? f.createClassInitializer(f.createStatic(), body) : f.createClassInitializer(body);
            ci.makeAllParentRolesValid();
            TypeDeclaration tdecl = fd.getMemberParent();
            attach(ci, tdecl, tdecl.getMembers().indexOf(fd) + 1);
        }
    }

    public NonTerminalProgramElement getTopMostParent() {
        return this.parent;
    }

    public Statement getEnclosingStatement() {
        if (this.newParent == null)
            throw new IllegalStateException("Only valid after transformation");
        return this.newParent;
    }
}
