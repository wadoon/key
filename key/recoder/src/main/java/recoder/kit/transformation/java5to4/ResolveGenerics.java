package recoder.kit.transformation.java5to4;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.abstraction.*;
import recoder.convenience.TreeWalker;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.expression.Assignment;
import recoder.java.expression.operator.New;
import recoder.java.reference.*;
import recoder.kit.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.CrossReferenceSourceInfo;
import recoder.service.SourceInfo;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class ResolveGenerics extends TwoPassTransformation {
    private final CompilationUnit cu;

    private List<TwoPassTransformation> parts;

    private List<ProgramElement> stuffToBeRemoved;

    private List<TwoPassTransformation> trParts;

    public ResolveGenerics(CrossReferenceServiceConfiguration sc, CompilationUnit cu) {
        super(sc);
        this.cu = cu;
    }

    private static void analyze(ProgramFactory f, CrossReferenceSourceInfo ci, List<TypeParameterDeclaration> typeParams, List<ProgramElement> stuffToBeRemoved, List<IntroduceCast> casts, List<TypeParamRefReplacement> typeParamReferences) {
        for (int i = 0, s = typeParams.size(); i < s; ) {
            TypeReference repl;
            ClassType resolvedType;
            TypeParameterDeclaration tpd = typeParams.get(i);
            if (tpd.getBounds() == null || tpd.getBounds().size() == 0) {
                resolvedType = ci.getServiceConfiguration().getNameInfo().getJavaLangObject();
                repl = TypeKit.createTypeReference(ci, resolvedType, tpd);
            } else {
                resolvedType = (ClassType) ci.getType(tpd.getBounds().get(0));
                repl = makeReplacement(f, tpd);
            }
            TypeParameterDeclaration typeParameterDeclaration1 = tpd;
            while (true) {
                List<TypeReference> tprl = ci.getReferences(typeParameterDeclaration1);
                for (int j = 0, t = tprl.size(); j < t; j++) {
                    TypeReference tr = tprl.get(j);
                    if (!(tr.getASTParent() instanceof TypeArgumentDeclaration)) {
                        typeParamReferences.add(new TypeParamRefReplacement(tr, repl.deepClone()));
                    } else {
                        stuffToBeRemoved.add(tr.getASTParent());
                    }
                    boolean alwaysCast = false;
                    while (tr.getASTParent() instanceof TypeArgumentDeclaration) {
                        tr = (TypeReference) tr.getASTParent().getASTParent();
                        alwaysCast = true;
                    }
                    if (tr.getASTParent() instanceof MethodDeclaration) {
                        MethodDeclaration md = (MethodDeclaration) tr.getASTParent();
                        List<MemberReference> mrl = ci.getReferences(md);
                        for (int k = 0; k < mrl.size(); k++) {
                            MethodReference mr = (MethodReference) mrl.get(k);
                            NonTerminalProgramElement parent = mr.getASTParent();
                            if (parent instanceof MethodReference) {
                                ClassType tmpResolved = resolvedType;
                                MethodReference pr = (MethodReference) parent;
                                while (true) {
                                    ClassType target = ci.getMethod(pr).getContainingClassType();
                                    if (target != null && !(target instanceof recoder.abstraction.TypeParameter) && (!ci.isSubtype(tmpResolved, target) || alwaysCast))
                                        casts.add(new IntroduceCast(mr, TypeKit.createTypeReference(ci, target, parent)));
                                    if (pr.getReferenceSuffix() instanceof MethodReference) {
                                        Type tmp = ci.getType(pr);
                                        if (!(tmp instanceof ClassType))
                                            break;
                                        tmpResolved = (ClassType) tmp;
                                        mr = pr;
                                        pr = (MethodReference) pr.getReferenceSuffix();
                                        continue;
                                    }
                                    break;
                                }
                            } else if (parent instanceof Expression || parent instanceof VariableSpecification || parent instanceof recoder.java.statement.Return) {
                                Type target;
                                if (parent instanceof recoder.java.statement.Return) {
                                    for (; !(parent instanceof MethodDeclaration); parent = parent.getASTParent()) ;
                                    target = ((MethodDeclaration) parent).getReturnType();
                                } else {
                                    target = ci.getType(parent);
                                }
                                if (!(target instanceof recoder.abstraction.PrimitiveType) && !ci.isSubtype(resolvedType, (ClassType) target) && !(target instanceof recoder.abstraction.TypeParameter))
                                    casts.add(new IntroduceCast(mr, TypeKit.createTypeReference(ci, target, mr)));
                                if (parent instanceof Assignment) {
                                    Assignment as = (Assignment) parent;
                                    if (as.getExpressionAt(0) == mr)
                                        casts.add(new IntroduceCast(as, TypeKit.createTypeReference(ci, target, as.getExpressionAt(1))));
                                }
                            }
                        }
                    }
                }
                ArrayType arrayType = ci.getServiceConfiguration().getNameInfo().getArrayType(typeParameterDeclaration1);
                repl.setDimensions(repl.getDimensions() + 1);
                if (arrayType == null)
                    i++;
            }
        }
    }

    private static TypeReference makeReplacement(ProgramFactory f, TypeParameterDeclaration tpd) {
        TypeReference repl = tpd.getBounds().get(0).deepClone();
        if (tpd.getBoundCount() > 1) {
            StringBuffer text = new StringBuffer("/*");
            for (int x = 1; x < tpd.getBoundCount(); x++) {
                text.append(" & ");
                text.append(tpd.getBoundName(x));
            }
            text.append(" */");
            repl.setComments(new ASTArrayList(f.createComment(text.toString(), false)));
        }
        return repl;
    }

    public ProblemReport analyze() {
        this.parts = new ArrayList<TwoPassTransformation>();
        this.stuffToBeRemoved = new ArrayList<ProgramElement>();
        this.trParts = new ArrayList<TwoPassTransformation>();
        TreeWalker tw = new TreeWalker(this.cu);
        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            NonTerminalProgramElement parent = pe.getASTParent();
            if (pe instanceof TypeDeclaration && !(pe instanceof TypeParameterDeclaration)) {
                ResolveSingleGenericType p = new ResolveSingleGenericType(getServiceConfiguration(), (TypeDeclaration) pe);
                if (p.analyze() != IDENTITY)
                    this.parts.add(p);
                continue;
            }
            if (pe instanceof MethodDeclaration) {
                ResolveGenericMethod p = new ResolveGenericMethod(getServiceConfiguration(), (MethodDeclaration) pe);
                if (p.analyze() != IDENTITY)
                    this.parts.add(p);
                continue;
            }
            if (pe instanceof TypeReference) {
                TwoPassTransformation p;
                TypeReference tr = (TypeReference) pe;
                if (parent instanceof MethodDeclaration) {
                    MethodDeclaration md = (MethodDeclaration) parent;
                    if (md.getTypeReference() != tr)
                        continue;
                    Type t = getSourceInfo().getType(tr);
                    if (t instanceof TypeDeclaration && !(t instanceof TypeParameterDeclaration)) {
                        CompilationUnit tcu = UnitKit.getCompilationUnit((ProgramElement) t);
                        if (tcu == this.cu)
                            continue;
                    }
                    p = new ResolveMethodReturnType(getServiceConfiguration(), md);
                } else if (parent instanceof VariableDeclaration) {
                    Type t = getSourceInfo().getType(tr);
                    if (t instanceof TypeDeclaration && !(t instanceof TypeParameterDeclaration)) {
                        CompilationUnit tcu = UnitKit.getCompilationUnit((ProgramElement) t);
                        if (tcu == this.cu)
                            continue;
                    }
                    VariableDeclaration vd = (VariableDeclaration) parent;
                    p = new ResolveSingleVariableDeclaration(getServiceConfiguration(), vd);
                } else {
                    if (parent instanceof InheritanceSpecification) {
                        Type t = getSourceInfo().getType(tr);
                        if (t instanceof TypeParameterDeclaration)
                            continue;
                        if (tr.getTypeArguments() == null)
                            continue;
                        List<? extends Method> ml = ((InheritanceSpecification) parent).getParent().getAllMethods();
                        for (int i = 0; i < ml.size(); i++) {
                            Method m = ml.get(i);
                            if (m instanceof recoder.bytecode.MethodInfo || UnitKit.getCompilationUnit((ProgramElement) m) != this.cu) {
                                p = new ResolveMethodReturnType(getServiceConfiguration(), m);
                                if (p.analyze() != IDENTITY)
                                    this.trParts.add(p);
                            }
                        }
                        this.stuffToBeRemoved.addAll(tr.getTypeArguments());
                        continue;
                    }
                    if (parent instanceof MethodReference && parent.getASTParent() instanceof MethodReference) {
                        Method m = getSourceInfo().getMethod((MethodReference) parent.getASTParent());
                        if (m instanceof recoder.bytecode.MethodInfo || UnitKit.getCompilationUnit((ProgramElement) m) != this.cu) {
                            p = new ResolveMethodReturnType(getServiceConfiguration(), m);
                        } else {
                            continue;
                        }
                    } else {
                        continue;
                    }
                }
                if (p.analyze() != IDENTITY)
                    this.trParts.add(p);
                continue;
            }
            if (pe instanceof New) {
                New n = (New) pe;
                if (n.getTypeReference().getTypeArguments() != null)
                    this.stuffToBeRemoved.addAll(n.getTypeReference().getTypeArguments());
            }
        }
        if (this.parts.size() == 0 && this.stuffToBeRemoved.size() == 0)
            return setProblemReport(IDENTITY);
        return super.analyze();
    }

    public void transform() {
        super.transform();
        for (int i = this.parts.size() - 1; i >= 0; i--)
            this.parts.get(i).transform();
        for (TwoPassTransformation tp : this.trParts)
            tp.transform();
        for (ProgramElement pe : this.stuffToBeRemoved) {
            if (pe.getASTParent().getIndexOfChild(pe) != -1)
                detach(pe);
        }
    }

    private static class IntroduceCast {
        Expression toBeCasted;

        TypeReference castedType;

        IntroduceCast(Expression e, TypeReference tr) {
            this.toBeCasted = e;
            this.castedType = tr;
        }
    }

    private static class TypeParamRefReplacement {
        TypeReference typeParamRef;

        TypeReference replacement;

        TypeParamRefReplacement(TypeReference from, TypeReference to) {
            this.typeParamRef = from;
            this.replacement = to;
            this.replacement.setTypeArguments(null);
        }
    }

    public static class ResolveSingleGenericType extends TwoPassTransformation {
        private final TypeDeclaration td;

        private List<ProgramElement> stuffToBeRemoved;

        private List<ResolveGenerics.IntroduceCast> casts;

        private List<ResolveGenerics.TypeParamRefReplacement> typeParamReferences;

        ResolveSingleGenericType(CrossReferenceServiceConfiguration sc, TypeDeclaration td) {
            super(sc);
            this.td = td;
        }

        public ProblemReport analyze() {
            ASTList aSTList = this.td.getTypeParameters();
            if (aSTList == null || aSTList.size() == 0)
                return setProblemReport(IDENTITY);
            this.stuffToBeRemoved = new ArrayList<ProgramElement>(100);
            this.casts = new ArrayList<ResolveGenerics.IntroduceCast>();
            this.typeParamReferences = new ArrayList<ResolveGenerics.TypeParamRefReplacement>();
            CrossReferenceSourceInfo ci = getCrossReferenceSourceInfo();
            ResolveGenerics.analyze(getProgramFactory(), ci, (List<TypeParameterDeclaration>) aSTList, this.stuffToBeRemoved, this.casts, this.typeParamReferences);
            List<TypeReference> trl = ci.getReferences(this.td);
            for (int i = 0, s = trl.size(); i < s; i++) {
                TypeReference tr = trl.get(i);
                ASTList aSTList1 = tr.getTypeArguments();
                if (aSTList1 != null && aSTList1.size() != 0)
                    this.stuffToBeRemoved.addAll((Collection<? extends ProgramElement>) aSTList1);
            }
            this.stuffToBeRemoved.addAll((Collection<? extends ProgramElement>) aSTList);
            return super.analyze();
        }

        public void transform() {
            super.transform();
            if (getProblemReport() == IDENTITY)
                return;
            ProgramFactory f = getProgramFactory();
            for (ResolveGenerics.IntroduceCast c : this.casts) {
                MiscKit.unindent(c.toBeCasted);
                if (!(c.toBeCasted.getASTParent() instanceof recoder.java.StatementContainer))
                    replace(c.toBeCasted, f.createParenthesizedExpression(f.createTypeCast(c.toBeCasted.deepClone(), c.castedType)));
            }
            for (ResolveGenerics.TypeParamRefReplacement t : this.typeParamReferences) {
                MiscKit.unindent(t.replacement);
                replace(t.typeParamRef, t.replacement);
            }
            for (ProgramElement tbr : this.stuffToBeRemoved) {
                if (tbr.getASTParent().getChildPositionCode(tbr) != -1)
                    detach(tbr);
            }
            MiscKit.unindent(this.td);
        }
    }

    public static class ResolveGenericMethod extends TwoPassTransformation {
        private final MethodDeclaration md;

        private List<ProgramElement> stuffToBeRemoved;

        private List<ResolveGenerics.IntroduceCast> casts;

        private List<ResolveGenerics.TypeParamRefReplacement> typeParamReferences;

        public ResolveGenericMethod(CrossReferenceServiceConfiguration sc, MethodDeclaration md) {
            super(sc);
            this.md = md;
        }

        public ProblemReport analyze() {
            ASTList aSTList = this.md.getTypeParameters();
            if (aSTList == null || aSTList.size() == 0)
                return setProblemReport(IDENTITY);
            ProgramFactory f = getProgramFactory();
            this.stuffToBeRemoved = new ArrayList<ProgramElement>(100);
            this.casts = new ArrayList<ResolveGenerics.IntroduceCast>();
            this.typeParamReferences = new ArrayList<ResolveGenerics.TypeParamRefReplacement>();
            CrossReferenceSourceInfo ci = getCrossReferenceSourceInfo();
            ResolveGenerics.analyze(f, ci, (List<TypeParameterDeclaration>) aSTList, this.stuffToBeRemoved, this.casts, this.typeParamReferences);
            List<MemberReference> mrl = ci.getReferences(this.md);
            for (int i = 0, s = mrl.size(); i < s; i++) {
                MethodReference mr = (MethodReference) mrl.get(i);
                ASTList aSTList1 = mr.getTypeArguments();
                if (aSTList1 != null && aSTList1.size() != 0)
                    this.stuffToBeRemoved.addAll((Collection<? extends ProgramElement>) aSTList1);
            }
            this.stuffToBeRemoved.addAll((Collection<? extends ProgramElement>) aSTList);
            return super.analyze();
        }

        public void transform() {
            super.transform();
            if (getProblemReport() == IDENTITY)
                return;
            ProgramFactory f = getProgramFactory();
            for (ResolveGenerics.IntroduceCast c : this.casts) {
                MiscKit.unindent(c.toBeCasted);
                if (!(c.toBeCasted.getASTParent() instanceof recoder.java.StatementContainer))
                    replace(c.toBeCasted, f.createParenthesizedExpression(f.createTypeCast(c.toBeCasted.deepClone(), c.castedType)));
            }
            for (ResolveGenerics.TypeParamRefReplacement t : this.typeParamReferences) {
                MiscKit.unindent(t.replacement);
                replace(t.typeParamRef, t.replacement);
            }
            for (ProgramElement tbr : this.stuffToBeRemoved) {
                if (tbr.getASTParent().getChildPositionCode(tbr) != -1)
                    detach(tbr);
            }
            MiscKit.unindent(this.md);
        }
    }

    public static class ResolveMethodReturnType extends TwoPassTransformation {
        private final Method md;

        private TypeReference tr;

        private List<ProgramElement> stuffToBeRemoved;

        private List<ResolveGenerics.IntroduceCast> casts;

        public ResolveMethodReturnType(CrossReferenceServiceConfiguration sc, Method md) {
            super(sc);
            this.md = md;
            if (md instanceof MethodDeclaration)
                this.tr = ((MethodDeclaration) md).getTypeReference();
        }

        public ProblemReport analyze() {
            Type returnType = this.md.getReturnType();
            if (!(returnType instanceof recoder.abstraction.ParameterizedType) && !(returnType instanceof recoder.abstraction.TypeParameter))
                return IDENTITY;
            CrossReferenceSourceInfo ci = getCrossReferenceSourceInfo();
            this.stuffToBeRemoved = new ArrayList<ProgramElement>();
            if (this.md instanceof MethodDeclaration &&
                    this.tr.getTypeArguments() != null)
                this.stuffToBeRemoved.addAll(this.tr.getTypeArguments());
            this.casts = new ArrayList<ResolveGenerics.IntroduceCast>();
            List<MemberReference> mrl = ci.getReferences(this.md);
            for (int j = 0, t = mrl.size(); j < t; j++) {
                MethodReference vr = (MethodReference) mrl.get(j);
                NonTerminalProgramElement parent = vr.getASTParent();
                while (parent instanceof MethodReference) {
                    Type ty = ci.getType((Expression) parent);
                    if (!(ty instanceof ClassType))
                        break;
                    if (!(ty instanceof recoder.abstraction.TypeParameter))
                        this.casts.add(new ResolveGenerics.IntroduceCast(vr, TypeKit.createTypeReference(ci, getSourceInfo().getType(vr), parent)));
                    ReferenceSuffix referenceSuffix = ((MethodReference) parent).getReferenceSuffix();
                }
            }
            return super.analyze();
        }

        public void transform() {
            ProgramFactory f = getProgramFactory();
            for (ResolveGenerics.IntroduceCast c : this.casts) {
                MiscKit.unindent(c.toBeCasted);
                if (c.toBeCasted.getASTParent().getIndexOfChild(c.toBeCasted) != -1 && !(c.toBeCasted.getASTParent() instanceof recoder.java.StatementContainer))
                    replace(c.toBeCasted, f.createParenthesizedExpression(f.createTypeCast(c.toBeCasted.deepClone(), c.castedType)));
            }
            if (this.md instanceof MethodDeclaration)
                for (ProgramElement pe : this.stuffToBeRemoved) {
                    if (pe.getASTParent().getIndexOfChild(pe) != -1)
                        detach(pe);
                }
        }
    }

    public static class ResolveSingleVariableDeclaration extends TwoPassTransformation {
        private final VariableDeclaration vd;

        private final TypeReference tr;

        private List<ProgramElement> stuffToBeRemoved;

        private List<ResolveGenerics.IntroduceCast> casts;

        public ResolveSingleVariableDeclaration(CrossReferenceServiceConfiguration sc, VariableDeclaration vd) {
            super(sc);
            this.vd = vd;
            this.tr = vd.getTypeReference();
        }

        public ProblemReport analyze() {
            if (this.tr.getTypeArguments() == null || this.tr.getTypeArguments().size() == 0)
                return IDENTITY;
            CrossReferenceSourceInfo ci = getCrossReferenceSourceInfo();
            this.stuffToBeRemoved = new ArrayList<ProgramElement>();
            this.stuffToBeRemoved.addAll(this.tr.getTypeArguments());
            this.casts = new ArrayList<ResolveGenerics.IntroduceCast>();
            for (int i = 0, s = this.vd.getVariables().size(); i < s; i++) {
                VariableSpecification vs = this.vd.getVariables().get(i);
                List<? extends VariableReference> vrl = ci.getReferences(vs);
                for (int j = 0, t = vrl.size(); j < t; j++) {
                    VariableReference vr = vrl.get(j);
                    NonTerminalProgramElement parent = vr.getASTParent();
                    while (parent instanceof MethodReference) {
                        Type ty = ci.getType((Expression) parent);
                        if (!(ty instanceof ClassType))
                            break;
                        if (!(ty instanceof recoder.abstraction.TypeParameter))
                            this.casts.add(new ResolveGenerics.IntroduceCast((Expression) parent, TypeKit.createTypeReference(ci, ty, parent)));
                        ReferenceSuffix referenceSuffix = ((MethodReference) parent).getReferenceSuffix();
                    }
                }
            }
            return super.analyze();
        }

        public void transform() {
            ProgramFactory f = getProgramFactory();
            for (ResolveGenerics.IntroduceCast c : this.casts) {
                MiscKit.unindent(c.toBeCasted);
                if (c.toBeCasted.getASTParent().getIndexOfChild(c.toBeCasted) != -1 && !(c.toBeCasted.getASTParent() instanceof recoder.java.StatementContainer))
                    replace(c.toBeCasted, f.createParenthesizedExpression(f.createTypeCast(c.toBeCasted.deepClone(), c.castedType)));
            }
            for (ProgramElement pe : this.stuffToBeRemoved) {
                if (pe.getASTParent().getIndexOfChild(pe) != -1)
                    detach(pe);
            }
        }
    }
}
