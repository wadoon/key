package recoder.kit;

import recoder.ModelElement;
import recoder.ProgramFactory;
import recoder.abstraction.Type;
import recoder.abstraction.Variable;
import recoder.convenience.Format;
import recoder.convenience.ProgramElementWalker;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.reference.TypeReference;
import recoder.java.reference.VariableReference;
import recoder.java.statement.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.ChangeHistory;
import recoder.service.CrossReferenceSourceInfo;
import recoder.service.SourceInfo;
import recoder.util.Debug;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class StatementKit {
    public static ASTList<Statement> prepareStatementMutableList(Statement s, ChangeHistory ch) {
        Debug.assertNonnull(s);
        StatementContainer con = s.getStatementContainer();
        if (con == null) {
            ASTArrayList aSTArrayList = new ASTArrayList();
            aSTArrayList.add(s);
            return (ASTList<Statement>) aSTArrayList;
        }
        ASTList<Statement> result = getStatementMutableList(s);
        if (result == null)
            result = wrapWithStatementBlock(s, ch).getBody();
        return result;
    }

    public static ASTList<Statement> getStatementMutableList(Statement s) {
        StatementBlock statementBlock;
        Debug.assertNonnull(s);
        StatementContainer con = s.getStatementContainer();
        if (con == null)
            return null;
        Statement body = null;
        if (con instanceof Statement) {
            if (con instanceof StatementBlock)
                return ((StatementBlock) con).getBody();
            if (con instanceof recoder.java.statement.Branch) {
                if (con instanceof Then) {
                    body = ((Then) con).getBody();
                } else if (con instanceof Else) {
                    body = ((Else) con).getBody();
                } else {
                    if (con instanceof Case)
                        return ((Case) con).getBody();
                    if (con instanceof Default)
                        return ((Default) con).getBody();
                    if (con instanceof Catch) {
                        body = ((Catch) con).getBody();
                    } else if (con instanceof Finally) {
                        body = ((Finally) con).getBody();
                    }
                }
            } else if (con instanceof Try) {
                statementBlock = ((Try) con).getBody();
            } else if (con instanceof SynchronizedBlock) {
                statementBlock = ((SynchronizedBlock) con).getBody();
            } else if (con instanceof LabeledStatement) {
                return getStatementMutableList((Statement) con);
            }
        } else if (con instanceof MemberDeclaration) {
            if (con instanceof MethodDeclaration) {
                statementBlock = ((MethodDeclaration) con).getBody();
            } else if (con instanceof ClassInitializer) {
                statementBlock = ((ClassInitializer) con).getBody();
            }
        }
        if (statementBlock == null)
            Debug.assertBoolean(true, "Could not handle container of statement " + Format.toString("%c \"%s\" @%p in %f", s));
        if (statementBlock instanceof StatementBlock && statementBlock != s)
            return statementBlock.getBody();
        return null;
    }

    public static StatementBlock wrapWithStatementBlock(Statement s, ChangeHistory ch) {
        Debug.assertNonnull(s);
        StatementContainer con = s.getStatementContainer();
        StatementBlock block = s.getFactory().createStatementBlock();
        if (con != null) {
            con.replaceChild(s, block);
            if (ch != null)
                ch.replaced(s, block);
        }
        block.setBody(new ASTArrayList(1));
        block.getBody().add(s);
        block.makeParentRoleValid();
        return block;
    }

    public static boolean canSafelyWrapWithStatementBlock(CrossReferenceSourceInfo xr, Statement s) {
        Debug.assertNonnull(xr, s);
        if (s instanceof LocalVariableDeclaration) {
            LocalVariableDeclaration lvd = (LocalVariableDeclaration) s;
            List<? extends VariableSpecification> vsl = lvd.getVariables();
            for (int j = vsl.size() - 1; j >= 0; j--) {
                Variable v = vsl.get(j);
                List<? extends VariableReference> vrl = xr.getReferences(v);
                for (int i = vrl.size() - 1; i >= 0; i--) {
                    if (!MiscKit.contains(lvd, vrl.get(i)))
                        return false;
                }
            }
        }
        return true;
    }

    public static void preparePrepend(ChangeHistory ch, SourceInfo si, ExpressionJumpStatement returnOrThrow) {
        Debug.assertNonnull(si, returnOrThrow);
        ASTList<Statement> aSTList = prepareStatementMutableList(returnOrThrow, ch);
        if (returnOrThrow.getExpressionCount() == 0)
            return;
        Expression expr = returnOrThrow.getExpressionAt(0);
        if (!ExpressionKit.containsStatements(expr))
            return;
        ProgramFactory f = returnOrThrow.getFactory();
        Type type = si.getType(expr);
        String vname = VariableKit.getNewVariableName(si, type, MiscKit.getScopeDefiningElement(expr));
        TypeReference tref = TypeKit.createTypeReference(si, type, expr);
        LocalVariableDeclaration lvd = f.createLocalVariableDeclaration(tref, f.createIdentifier(vname));
        lvd.getVariables().get(0).setInitializer(expr);
        lvd.makeAllParentRolesValid();
        VariableReference vref = f.createVariableReference(f.createIdentifier(vname));
        returnOrThrow.replaceChild(expr, vref);
        if (ch != null)
            ch.replaced(expr, vref);
        StatementContainer destParent = returnOrThrow.getStatementContainer();
        int idx;
        for (idx = 0; aSTList.get(idx) != returnOrThrow; idx++) ;
        aSTList.add(idx, lvd);
        lvd.setStatementContainer(destParent);
        if (ch != null)
            ch.attached(lvd);
    }

    public static boolean isReachable(Statement s, SourceInfo si) {
        MemberDeclaration member = MiscKit.getParentMemberDeclaration(s);
        ControlFlowWalker w = new ControlFlowWalker(member, si);
        while (w.next()) {
            if (w.getStatement() == s)
                return true;
        }
        return false;
    }

    public static boolean hasReachableEnd(StatementBlock block, SourceInfo si) {
        ASTList<EmptyStatement> aSTList = block.getBody();
        if (aSTList == null || aSTList.isEmpty())
            return true;
        EmptyStatement emptyStatement = block.getFactory().createEmptyStatement();
        aSTList.add(emptyStatement);
        emptyStatement.setStatementContainer(block);
        boolean result = isReachable(emptyStatement, si);
        aSTList.remove(aSTList.size() - 1);
        return result;
    }

    public static LabeledStatement getCorrespondingLabel(LabelJumpStatement s) {
        String idText = s.getIdentifier().getText();
        NonTerminalProgramElement parent = s.getASTParent();
        while (parent != null) {
            if (parent instanceof LabeledStatement) {
                LabeledStatement lstat = (LabeledStatement) parent;
                if (idText.equals(lstat.getIdentifier().getText()))
                    return lstat;
            }
            parent = parent.getASTParent();
        }
        return null;
    }

    public static List<Statement> getExits(MemberDeclaration mdecl, SourceInfo si) {
        Debug.assertNonnull(mdecl, si);
        List<Statement> result = new ArrayList<Statement>();
        StatementBlock body = null;
        if (mdecl instanceof MethodDeclaration) {
            body = ((MethodDeclaration) mdecl).getBody();
        } else if (mdecl instanceof ClassInitializer) {
            body = ((ClassInitializer) mdecl).getBody();
        }
        if (body == null)
            return new ArrayList<Statement>(0);
        EmptyStatement emptyStatement = body.getFactory().createEmptyStatement();
        int s = (body.getBody() == null) ? 0 : body.getBody().size();
        Transformation.doAttach(emptyStatement, body, s);
        ControlFlowWalker w = new ControlFlowWalker(mdecl, si);
        while (w.next()) {
            ProgramElement p = w.getProgramElement();
            if (p == emptyStatement) {
                result.add(body);
                continue;
            }
            if (p instanceof ExpressionJumpStatement)
                result.add((Statement) p);
        }
        Transformation.doDetach(emptyStatement);
        return result;
    }

    public static class ControlFlowWalker implements ProgramElementWalker {
        private final SourceInfo si;

        private Statement current;

        private List<Statement> successors;

        private final Set<Statement> reached;

        private final List<Statement> stack;

        public ControlFlowWalker(MemberDeclaration parent, SourceInfo si) {
            if (si == null || parent == null)
                throw new IllegalArgumentException();
            this.si = si;
            this.reached = new HashSet<Statement>();
            this.stack = new ArrayList<Statement>();
            if (parent instanceof MethodDeclaration) {
                StatementBlock body = ((MethodDeclaration) parent).getBody();
                if (body != null)
                    this.stack.add(body);
            } else if (parent instanceof ClassInitializer) {
                StatementBlock body = ((ClassInitializer) parent).getBody();
                if (body != null)
                    this.stack.add(body);
            }
        }

        public boolean next() {
            int size = this.stack.size();
            if (size == 0) {
                this.current = null;
                this.successors = null;
                return false;
            }
            this.current = this.stack.get(size - 1);
            this.reached.add(this.current);
            this.stack.remove(size - 1);
            this.successors = this.si.getSucceedingStatements(this.current);
            for (int i = 0, s = this.successors.size(); i < s; i++) {
                Statement f = this.successors.get(i);
                if (f != SourceInfo.METHOD_EXIT && !this.reached.contains(f))
                    this.stack.add(f);
            }
            return true;
        }

        public ProgramElement getProgramElement() {
            return this.current;
        }

        public Statement getStatement() {
            return this.current;
        }

        public List<Statement> getSucceedingStatements() {
            return this.successors;
        }

        public boolean isReachable(Statement s) {
            return this.reached.contains(s);
        }
    }
}
