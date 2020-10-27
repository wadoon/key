package recoder.kit;

import recoder.ProgramFactory;
import recoder.abstraction.Type;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.expression.Literal;
import recoder.java.expression.Operator;
import recoder.java.expression.operator.CopyAssignment;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.ReferenceSuffix;
import recoder.java.reference.TypeReference;
import recoder.java.reference.VariableReference;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.ChangeHistory;
import recoder.service.NameInfo;
import recoder.service.SourceInfo;
import recoder.util.Debug;

import java.util.Collection;
import java.util.List;

public class ExpressionKit {
    public static boolean containsStatements(Expression expr) {
        if (expr instanceof Statement &&
                !(expr instanceof recoder.java.expression.ParenthesizedExpression))
            return true;
        if (expr instanceof ExpressionContainer) {
            ExpressionContainer con = (ExpressionContainer) expr;
            for (int i = 0, s = con.getExpressionCount(); i < s; i++) {
                if (containsStatements(con.getExpressionAt(i)))
                    return true;
            }
        }
        return false;
    }

    public static boolean isLValue(Expression r) {
        if (r instanceof VariableReference || r instanceof recoder.java.reference.ArrayReference) {
            ExpressionContainer c = r.getExpressionContainer();
            return (c instanceof recoder.java.expression.Assignment && c.getExpressionAt(0) == r);
        }
        return false;
    }

    public static List<Expression> collectPreceedingExpressions(Expression x) {
        Debug.assertNonnull(x);
        ASTArrayList<Expression> aSTArrayList = new ASTArrayList();
        if (x instanceof recoder.java.reference.MethodReference || x instanceof recoder.java.reference.ConstructorReference) {
            ExpressionContainer ec = (ExpressionContainer) x;
            for (int i = 0, s = ec.getExpressionCount(); i < s; i++)
                aSTArrayList.add(ec.getExpressionAt(i));
        } else if (x instanceof ReferenceSuffix) {
            ReferencePrefix rp = ((ReferenceSuffix) x).getReferencePrefix();
            if (rp instanceof Expression)
                aSTArrayList.add((Expression) rp);
        }
        while (true) {
            boolean leftAssociative;
            ExpressionContainer parent = x.getExpressionContainer();
            if (parent == null)
                return aSTArrayList;
            if (parent instanceof Operator) {
                leftAssociative = ((Operator) parent).isLeftAssociative();
            } else {
                leftAssociative = true;
            }
            if (leftAssociative) {
                int i = 0;
                if (parent instanceof ReferenceSuffix && (
                        (ReferenceSuffix) parent).getReferencePrefix() instanceof Expression)
                    i = 1;
                Expression expr;
                while ((expr = parent.getExpressionAt(i)) != x) {
                    aSTArrayList.add(expr);
                    i++;
                }
            } else {
                Expression expr;
                for (int i = parent.getExpressionCount() - 1; (expr = parent.getExpressionAt(i)) != x; i--)
                    aSTArrayList.add(expr);
            }
            if (!(parent instanceof Expression))
                return aSTArrayList;
            x = (Expression) parent;
        }
    }

    public static boolean shiftPreceedingStatementExpressions(SourceInfo si, Expression x, ChangeHistory ch) {
        ASTArrayList aSTArrayList1;
        ClassInitializer classInitializer;
        List<Expression> exprs = collectPreceedingExpressions(x);
        for (int i = exprs.size() - 1; i >= 0; i--) {
            if (!containsStatements(exprs.get(i)))
                exprs.remove(i);
        }
        if (exprs.isEmpty())
            return false;
        ProgramFactory f = x.getFactory();
        int exSize = exprs.size();
        ASTArrayList<LocalVariableDeclaration> aSTArrayList = new ASTArrayList(exSize);
        ScopeDefiningElement sde = MiscKit.getScopeDefiningElement(x);
        Type[] exTypes = new Type[exSize];
        for (int j = 0; j < exSize; j++) {
            Expression ex = exprs.get(j);
            exTypes[j] = si.getType(ex);
        }
        String[] varNames = VariableKit.getNewVariableNames(si, exTypes, sde);
        for (int k = 0; k < exSize; k++) {
            Expression ex = exprs.get(k);
            Type t = exTypes[k];
            TypeReference minTypeRef = TypeKit.createTypeReference(si, t, sde);
            String varName = varNames[k];
            LocalVariableDeclaration lvd = f.createLocalVariableDeclaration(minTypeRef, f.createIdentifier(varName));
            lvd.getVariables().get(0).setInitializer(ex);
            aSTArrayList.add(lvd);
            VariableReference vref = f.createVariableReference(f.createIdentifier(varName));
            ex.getASTParent().replaceChild(ex, vref);
            Debug.assertNonnull(vref.getASTParent());
            if (ch != null)
                ch.replaced(ex, vref);
        }
        ASTList<Statement> destination = null;
        NonTerminalProgramElement destParent = null;
        int destIndex = 0;
        Expression expression = x;
        while (true) {
            NonTerminalProgramElement parent = expression.getASTParent();
            Debug.assertNonnull(parent);
            if (parent instanceof Statement && ((Statement) parent).getStatementContainer() != null) {
                Statement parentStatement = (Statement) parent;
                destination = StatementKit.prepareStatementMutableList(parentStatement, ch);
                StatementContainer statementContainer = parentStatement.getStatementContainer();
                for (destIndex = 0; destination.get(destIndex) != parent; destIndex++) ;
                break;
            }
            if (parent instanceof FieldSpecification) {
                ClassInitializer ci;
                FieldSpecification fs = (FieldSpecification) parent;
                FieldDeclaration fd = (FieldDeclaration) fs.getParent();
                aSTArrayList1 = new ASTArrayList();
                StatementBlock body = f.createStatementBlock(aSTArrayList1);
                if (fd.isStatic()) {
                    ci = f.createClassInitializer(f.createStatic(), body);
                } else {
                    ci = f.createClassInitializer(body);
                }
                classInitializer = ci;
                TypeDeclaration tdecl = fd.getMemberParent();
                ASTList<ClassInitializer> aSTList = tdecl.getMembers();
                aSTList.add(aSTList.indexOf(fd) + 1, ci);
                ci.setMemberParent(tdecl);
                if (ch != null)
                    ch.attached(ci);
                Expression init = fs.getInitializer();
                int initIndex = fs.getChildPositionCode(init);
                fs.setInitializer(null);
                if (ch != null)
                    ch.detached(init, initIndex);
                CopyAssignment ca = f.createCopyAssignment(f.createVariableReference(f.createIdentifier(fs.getName())), init);
                ca.makeAllParentRolesValid();
                aSTArrayList1.add(ca);
                destIndex = 0;
                break;
            }
            NonTerminalProgramElement nonTerminalProgramElement1 = parent;
        }
        aSTArrayList1.addAll(destIndex, aSTArrayList);
        classInitializer.makeAllParentRolesValid();
        if (ch != null)
            for (int m = 0; m < aSTArrayList.size(); m++)
                ch.attached(aSTArrayList.get(m));
        return true;
    }

    public static Literal createDefaultValue(ProgramFactory f, NameInfo ni, Type t) {
        Debug.assertNonnull(f, ni, t);
        if (t instanceof recoder.abstraction.PrimitiveType) {
            if (t == ni.getIntType())
                return f.createIntLiteral(0);
            if (t == ni.getBooleanType())
                return f.createBooleanLiteral(false);
            if (t == ni.getCharType())
                return f.createCharLiteral(false);
            if (t == ni.getShortType())
                return f.createIntLiteral(0);
            if (t == ni.getByteType())
                return f.createIntLiteral(0);
            if (t == ni.getLongType())
                return f.createLongLiteral(0L);
            if (t == ni.getFloatType())
                return f.createFloatLiteral(0.0F);
            if (t == ni.getDoubleType())
                return f.createDoubleLiteral(0.0D);
            throw new IllegalArgumentException("Unknown primitive type " + t.getName());
        }
        return f.createNullLiteral();
    }
}
