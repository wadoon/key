package recoder.kit.transformation.java5to4;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ModelException;
import recoder.ProgramFactory;
import recoder.abstraction.Field;
import recoder.convenience.TreeWalker;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.expression.operator.LogicalOr;
import recoder.java.expression.operator.New;
import recoder.java.expression.operator.NewArray;
import recoder.java.reference.FieldReference;
import recoder.java.reference.ReferencePrefix;
import recoder.java.statement.*;
import recoder.kit.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

import java.util.*;

public class ReplaceEnums extends TwoPassTransformation {
    private final CompilationUnit cu;

    private List<ReplaceSingleEnum> parts;

    public ReplaceEnums(CrossReferenceServiceConfiguration sc, CompilationUnit cu) {
        super(sc);
        this.cu = cu;
    }

    public ProblemReport analyze() {
        this.parts = new ArrayList<ReplaceSingleEnum>();
        TreeWalker tw = new TreeWalker(this.cu);
        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            if (pe instanceof EnumDeclaration) {
                ReplaceSingleEnum p = new ReplaceSingleEnum(getServiceConfiguration(), (EnumDeclaration) pe);
                p.analyze();
                this.parts.add(p);
            }
        }
        return super.analyze();
    }

    public void transform() {
        super.transform();
        for (int i = this.parts.size() - 1; i >= 0; i--)
            this.parts.get(i).transform();
    }

    public class ReplaceSingleEnum extends TwoPassTransformation {
        private final EnumDeclaration ed;

        private ClassDeclaration repl;

        private Set<Switch> switchStmnts;

        private Map<Switch, String[]> names;

        public ReplaceSingleEnum(CrossReferenceServiceConfiguration sc, EnumDeclaration ed) {
            super(sc);
            this.ed = ed;
        }

        public ProblemReport analyze() {
            this.switchStmnts = new HashSet<Switch>();
            this.names = (Map) new HashMap<Switch, String>();
            ProgramFactory f = getProgramFactory();
            this.repl = f.createClassDeclaration();
            if (this.ed.getDeclarationSpecifiers() != null) {
                this.repl.setDeclarationSpecifiers(this.ed.getDeclarationSpecifiers().deepClone());
            } else {
                this.repl.setDeclarationSpecifiers(new ASTArrayList(1));
            }
            if (this.ed.isFinal())
                this.repl.getDeclarationSpecifiers().add(f.createFinal());
            if (this.ed.getComments() != null)
                this.repl.setComments(this.ed.getComments().deepClone());
            ASTArrayList<MemberDeclaration> mlist = new ASTArrayList(this.ed.getMembers().size());
            this.repl.setMembers(mlist);
            this.repl.setIdentifier(this.ed.getIdentifier().deepClone());
            ASTArrayList<FieldSpecification> enumSpecRepl = new ASTArrayList();
            for (int i = 0; i < this.ed.getMembers().size(); i++) {
                MemberDeclaration md = this.ed.getMembers().get(i);
                if (md instanceof EnumConstantDeclaration) {
                    EnumConstantDeclaration ec = (EnumConstantDeclaration) md;
                    EnumConstantSpecification ecs = ec.getEnumConstantSpecification();
                    ASTArrayList<DeclarationSpecifier> dsml = new ASTArrayList();
                    if (ec.getAnnotations() == null)
                        for (AnnotationUseSpecification a : ec.getAnnotations())
                            dsml.add(a.deepClone());
                    dsml.add(f.createFinal());
                    dsml.add(f.createPublic());
                    dsml.add(f.createStatic());
                    FieldDeclaration fd = f.createFieldDeclaration(dsml, f.createTypeReference(this.ed.getIdentifier().deepClone()), ecs.getIdentifier().deepClone(), null);
                    FieldSpecification fs = fd.getFieldSpecifications().get(0);
                    List<FieldReference> frl = getCrossReferenceSourceInfo().getReferences(ecs);
                    for (int k = 0; k < frl.size(); k++) {
                        FieldReference fr = frl.get(k);
                        if (fr.getASTParent() instanceof Case) {
                            Switch sw = (Switch) fr.getASTParent().getASTParent();
                            this.switchStmnts.add(sw);
                            String fallThroughName = VariableKit.createValidVariableName(getSourceInfo(), sw, "fallThrough");
                            String doneAnyName = VariableKit.createValidVariableName(getSourceInfo(), sw, "doneAny");
                            this.names.put(sw, new String[]{fallThroughName, doneAnyName});
                        }
                    }
                    New e = f.createNew();
                    e.setTypeReference(f.createTypeReference(this.repl.getIdentifier()));
                    if (ecs.getConstructorReference().getArguments() != null || ecs.getConstructorReference().getClassDeclaration() != null) {
                        ASTList<Expression> aSTList = ecs.getConstructorReference().getArguments();
                        int s = (aSTList == null) ? 0 : aSTList.size();
                        ASTArrayList<Expression> args = new ASTArrayList(s);
                        e.setArguments(args);
                        for (int m = 0; m < s; m++)
                            args.add(aSTList.get(m).deepClone());
                        if (ecs.getConstructorReference().getClassDeclaration() != null)
                            e.setClassDeclaration(ecs.getConstructorReference().getClassDeclaration().deepClone());
                    }
                    fs.setInitializer(e);
                    e.makeParentRoleValid();
                    fs.makeParentRoleValid();
                    fd.makeParentRoleValid();
                    enumSpecRepl.add(fs);
                    mlist.add(fd);
                } else {
                    mlist.add(md.deepClone());
                }
            }
            MethodDeclaration values = f.createMethodDeclaration();
            MethodDeclaration valueOf = f.createMethodDeclaration();
            MethodDeclaration ordinal = f.createMethodDeclaration();
            values.setIdentifier(f.createIdentifier("values"));
            valueOf.setIdentifier(f.createIdentifier("valueOf"));
            ordinal.setIdentifier(f.createIdentifier("ordinal"));
            ASTArrayList<DeclarationSpecifier> declSpecs = new ASTArrayList();
            declSpecs.add(f.createPublic());
            declSpecs.add(f.createStatic());
            values.setDeclarationSpecifiers(declSpecs);
            declSpecs = declSpecs.deepClone();
            valueOf.setDeclarationSpecifiers(declSpecs);
            declSpecs = declSpecs.deepClone();
            declSpecs.remove(1);
            declSpecs.add(f.createFinal());
            ordinal.setDeclarationSpecifiers(declSpecs);
            values.setTypeReference(f.createTypeReference(this.repl.getIdentifier().deepClone(), 1));
            valueOf.setTypeReference(f.createTypeReference(this.repl.getIdentifier().deepClone()));
            ordinal.setTypeReference(f.createTypeReference(f.createIdentifier("int")));
            valueOf.setParameters(new ASTArrayList(f.createParameterDeclaration(TypeKit.createTypeReference(f, "String"), f.createIdentifier("name"))));
            StatementBlock valuesSt = f.createStatementBlock();
            StatementBlock valueOfSt = f.createStatementBlock();
            StatementBlock ordinalSt = f.createStatementBlock();
            values.setBody(valuesSt);
            valueOf.setBody(valueOfSt);
            ordinal.setBody(ordinalSt);
            ordinalSt.setBody(new ASTArrayList(f.createReturn(f.createFieldReference(f.createIdentifier("ordinal")))));
            NewArray na = f.createNewArray();
            na.setTypeReference(f.createTypeReference(this.repl.getIdentifier().deepClone(), 1));
            na.setArrayInitializer(f.createArrayInitializer(new ASTArrayList(enumSpecRepl.size())));
            na.makeParentRoleValid();
            valuesSt.setBody(new ASTArrayList(f.createReturn(na)));
            If ite = f.createIf();
            valueOfSt.setBody(new ASTArrayList(ite));
            for (int j = 0; j < enumSpecRepl.size(); j++) {
                FieldSpecification fs = enumSpecRepl.get(j);
                na.getArrayInitializer().getArguments().add(f.createFieldReference(fs.getIdentifier().deepClone()));
                ite.setExpression(f.createMethodReference(f.createVariableReference(f.createIdentifier("name")), f.createIdentifier("equals"), new ASTArrayList(f.createStringLiteral("\"" + fs.getName() + "\""))));
                ite.setThen(f.createThen(f.createReturn(f.createFieldReference(fs.getIdentifier().deepClone()))));
                if (j + 1 < enumSpecRepl.size()) {
                    ite.setElse(f.createElse(f.createIf()));
                    ite.makeParentRoleValid();
                    ite = (If) ite.getElse().getStatementAt(0);
                } else {
                    ite.makeParentRoleValid();
                }
            }
            na.getArrayInitializer().makeParentRoleValid();
            ite.setElse(f.createElse(f.createThrow(f.createNew(null, f.createTypeReference(f.createIdentifier("IllegalArgumentException")), null))));
            ite.makeParentRoleValid();
            valuesSt.makeParentRoleValid();
            valueOfSt.makeParentRoleValid();
            ordinalSt.makeParentRoleValid();
            valueOf.makeParentRoleValid();
            values.makeParentRoleValid();
            ordinal.makeParentRoleValid();
            mlist.add(valueOf);
            mlist.add(values);
            mlist.add(ordinal);
            declSpecs = new ASTArrayList(2);
            declSpecs.add(f.createPrivate());
            declSpecs.add(f.createStatic());
            mlist.add(f.createFieldDeclaration(declSpecs, f.createTypeReference(f.createIdentifier("int")), f.createIdentifier("CURRENT_ORDINAL"), f.createIntLiteral("0")));
            declSpecs = new ASTArrayList(2);
            declSpecs.add(f.createPrivate());
            declSpecs.add(f.createFinal());
            mlist.add(f.createFieldDeclaration(declSpecs, f.createTypeReference(f.createIdentifier("int")), f.createIdentifier("ordinal"), f.createPostIncrement(f.createFieldReference(f.createIdentifier("CURRENT_ORDINAL")))));
            this.repl.makeParentRoleValid();
            MiscKit.unindent(this.repl);
            return super.analyze();
        }

        public void transform() {
            super.transform();
            replace(this.ed, this.repl);
            for (Switch sw : this.switchStmnts) {
                ProgramFactory f = getProgramFactory();
                ASTArrayList<Statement> sml = new ASTArrayList();
                StatementBlock sb = f.createStatementBlock(sml);
                String[] nm = this.names.get(sw);
                String fallThroughName = nm[0];
                String doneAnyName = nm[1];
                sml.add(f.createLocalVariableDeclaration(null, f.createTypeReference(f.createIdentifier("boolean")), f.createIdentifier(fallThroughName), f.createBooleanLiteral(false)));
                sml.add(f.createLocalVariableDeclaration(null, f.createTypeReference(f.createIdentifier("boolean")), f.createIdentifier(doneAnyName), f.createBooleanLiteral(false)));
                Do repl = f.createDo(f.createBooleanLiteral(false), sb);
                for (int i = 0; i < sw.getBranchCount(); i++) {
                    Branch b = sw.getBranchAt(i);
                    if (b instanceof Default) {
                        if (i != sw.getBranchCount() - 1)
                            throw new ModelException("case after default is illegal");
                        Default d = (Default) b;
                        ASTArrayList<Statement> defaultStmnt = new ASTArrayList();
                        StatementBlock sb2 = f.createStatementBlock(defaultStmnt);
                        LogicalOr cond = f.createLogicalOr(f.createVariableReference(f.createIdentifier(doneAnyName)), f.createVariableReference(f.createIdentifier(fallThroughName)));
                        defaultStmnt.addAll(d.getBody().deepClone());
                        sb2.makeParentRoleValid();
                        Then then = f.createThen(sb2);
                        If newIf = f.createIf(cond, then);
                        sml.add(newIf);
                    } else {
                        Case c = (Case) b;
                        LogicalOr cond = f.createLogicalOr(f.createVariableReference(f.createIdentifier(fallThroughName)), f.createEquals(f.createFieldReference(TypeKit.createTypeReference(f, this.ed.getFullName()), f.createIdentifier(((FieldReference) c.getExpression()).getName())), sw.getExpression().deepClone()));
                        ASTArrayList<Statement> thenStmnt = new ASTArrayList();
                        StatementBlock sb2 = f.createStatementBlock(thenStmnt);
                        thenStmnt.add(f.createCopyAssignment(f.createVariableReference(f.createIdentifier(doneAnyName)), f.createBooleanLiteral(true)));
                        thenStmnt.add(f.createCopyAssignment(f.createVariableReference(f.createIdentifier(fallThroughName)), f.createBooleanLiteral(false)));
                        thenStmnt.addAll(c.getBody().deepClone());
                        if (c.getBody().size() == 0 || !(c.getBody().get(c.getBody().size() - 1) instanceof recoder.java.statement.JumpStatement))
                            thenStmnt.add(f.createCopyAssignment(f.createVariableReference(f.createIdentifier(fallThroughName)), f.createBooleanLiteral(true)));
                        sb2.makeParentRoleValid();
                        Then then = f.createThen(sb2);
                        If newIf = f.createIf(cond, then);
                        sml.add(newIf);
                    }
                }
                sb.makeParentRoleValid();
                MiscKit.unindent(repl);
                replace(sw, repl);
            }
        }
    }
}
