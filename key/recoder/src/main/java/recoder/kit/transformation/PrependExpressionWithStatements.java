package recoder.kit.transformation;

import recoder.CrossReferenceServiceConfiguration;
import recoder.java.*;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.ChangeHistory;

import java.util.Collection;

public class PrependExpressionWithStatements extends TwoPassTransformation {
    private final Expression expression;

    private final ASTList<Statement> statements;

    private ShiftPreceedingStatementExpressions shifter;

    public PrependExpressionWithStatements(CrossReferenceServiceConfiguration sc, Expression x, ASTList<Statement> statements) {
        super(sc);
        if (x == null)
            throw new IllegalArgumentException("Missing expression");
        if (statements == null)
            throw new IllegalArgumentException("Missing statements");
        this.expression = x;
        this.statements = statements;
    }

    public PrependExpressionWithStatements(CrossReferenceServiceConfiguration sc, Expression x, Statement statement) {
        this(sc, x, (ASTList<Statement>) new ASTArrayList(statement));
    }

    public ProblemReport analyze() {
        if (this.statements.isEmpty())
            return setProblemReport(IDENTITY);
        this.shifter = new ShiftPreceedingStatementExpressions(getServiceConfiguration(), this.expression);
        ProblemReport report = this.shifter.analyze();
        if (report instanceof recoder.kit.Problem)
            return setProblemReport(report);
        if (report == IDENTITY) {
            Statement parent = (Statement) this.shifter.getTopMostParent();
            StatementContainer grandpa = parent.getStatementContainer();
            int i = 0;
            for (int s = grandpa.getStatementCount(); i < s &&
                    grandpa.getStatementAt(i) != parent; i++)
                ;
            int j = this.statements.size();
            if (i >= j) {
                j--;
                i--;
                while (j >= 0 &&
                        ProgramElement.STRUCTURAL_EQUALITY.equals(this.statements.get(j), grandpa.getStatementAt(i))) {
                    j--;
                    i--;
                }
                if (j < 0)
                    return setProblemReport(report);
            }
        }
        return setProblemReport(NO_PROBLEM);
    }

    public void transform() {
        super.transform();
        this.shifter.transform();
        Statement statement = this.shifter.getEnclosingStatement();
        PrepareStatementList preparer = new PrepareStatementList(getServiceConfiguration(), statement, true);
        preparer.execute();
        ASTList<Statement> body = preparer.getStatementList();
        statement = preparer.getStatement();
        int position = body.indexOf(statement);
        body.addAll(position, this.statements);
        ChangeHistory ch = getChangeHistory();
        StatementContainer parent = statement.getStatementContainer();
        for (int i = 0; i < this.statements.size(); i++) {
            Statement s = this.statements.get(i);
            s.setStatementContainer(parent);
            if (isVisible())
                ch.attached(s);
        }
    }
}
