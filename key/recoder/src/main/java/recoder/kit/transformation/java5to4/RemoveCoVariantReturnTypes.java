package recoder.kit.transformation.java5to4;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ModelException;
import recoder.ProgramFactory;
import recoder.abstraction.*;
import recoder.convenience.TreeWalker;
import recoder.java.Expression;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.TypeArgumentDeclaration;
import recoder.java.reference.MemberReference;
import recoder.java.reference.MethodReference;
import recoder.java.reference.TypeReference;
import recoder.kit.MethodKit;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.kit.TypeKit;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.DefaultSourceInfo;
import recoder.service.ProgramModelInfo;

import java.util.ArrayList;
import java.util.List;

public class RemoveCoVariantReturnTypes extends TwoPassTransformation {
    private final NonTerminalProgramElement root;

    private List<Item> items;

    public RemoveCoVariantReturnTypes(CrossReferenceServiceConfiguration sc, NonTerminalProgramElement root) {
        super(sc);
        this.root = root;
    }

    public ProblemReport analyze() {
        this.items = new ArrayList<Item>();
        TreeWalker tw = new TreeWalker(this.root);
        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            if (pe instanceof MethodDeclaration) {
                MethodDeclaration md = (MethodDeclaration) pe;
                Type returnType = getSourceInfo().getReturnType(md);
                if (returnType == null || returnType instanceof recoder.abstraction.PrimitiveType)
                    continue;
                List<Method> ml = MethodKit.getRedefinedMethods(md);
                if (ml.size() == 0)
                    continue;
                List<ClassType> ctml = new ArrayList<ClassType>(ml.size());
                for (int i = 0; i < ml.size(); i++) {
                    Type rt = getSourceInfo().getReturnType(ml.get(i));
                    if (rt instanceof ClassType && ctml.indexOf(rt) == -1)
                        ctml.add((ClassType) rt);
                }
                List<ClassType> ctml_copy = new ArrayList<ClassType>();
                ctml_copy.addAll(ctml);
                TypeKit.removeCoveredSubtypes(getSourceInfo(), ctml);
                if (ctml.size() != 1) {
                    if (ctml.size() == 0 && returnType instanceof recoder.abstraction.ArrayType)
                        continue;
                    throw new ModelException();
                }
                Type originalType = ctml.get(0);
                if (((DefaultSourceInfo) getSourceInfo()).containsTypeParameter(originalType))
                    originalType = makeSomething(originalType);
                if (originalType != returnType) {
                    TypeReference originalTypeReference = TypeKit.createTypeReference(getProgramFactory(), originalType);
                    TypeReference castToReference = TypeKit.createTypeReference(getProgramFactory(), returnType);
                    ASTList<TypeArgumentDeclaration> targs = md.getTypeReference().getTypeArguments();
                    if (targs != null && targs.size() > 0)
                        castToReference.setTypeArguments(targs.deepClone());
                    if (originalType instanceof ParameterizedType) {
                        ParameterizedType pt = (ParameterizedType) originalType;
                        targs = TypeKit.makeTypeArgRef(getProgramFactory(), pt.getTypeArgs());
                        originalTypeReference.setTypeArguments(targs);
                    }
                    this.items.add(new Item(md, getCrossReferenceSourceInfo().getReferences(md), originalTypeReference, castToReference));
                }
            }
        }
        return super.analyze();
    }

    private Type makeSomething(Type originalType) {
        if (originalType instanceof ParameterizedType) {
            ParameterizedType pt = (ParameterizedType) originalType;
            ClassType baseType = (ClassType) makeSomething0(pt.getGenericType());
            ASTArrayList aSTArrayList = new ASTArrayList(pt.getTypeArgs().size());
            for (TypeArgument ta : pt.getTypeArgs())
                aSTArrayList.add(makeSomething1(ta));
            return new ParameterizedType(baseType, aSTArrayList);
        }
        return makeSomething0(originalType);
    }

    private Type makeSomething0(Type originalType) {
        ClassType classType;
        if (!(originalType instanceof TypeParameter))
            return originalType;
        TypeParameter tp = (TypeParameter) originalType;
        if (tp.getBoundCount() == 0) {
            classType = getNameInfo().getJavaLangObject();
        } else {
            String tname = tp.getBoundName(0);
            classType = getNameInfo().getClassType(tname);
            if (classType.isInterface())
                classType = getNameInfo().getJavaLangObject();
        }
        return classType;
    }

    private TypeArgumentDeclaration makeSomething1(TypeArgument ta) {
        TypeArgumentDeclaration res = new TypeArgumentDeclaration();
        res.setTypeReference(TypeKit.createTypeReference(getProgramFactory(), ta.getTypeName()));
        if (ta.getTypeArguments() != null && ta.getTypeArguments().size() > 0) {
            ASTArrayList aSTArrayList = new ASTArrayList(ta.getTypeArguments().size());
            for (TypeArgument t : ta.getTypeArguments())
                aSTArrayList.add(makeSomething1(t));
            res.getTypeReference().setTypeArguments(aSTArrayList);
            res.getTypeReference().makeParentRoleValid();
        }
        return res;
    }

    public void transform() {
        super.transform();
        ProgramFactory f = getProgramFactory();
        for (Item it : this.items) {
            replace(it.md.getTypeReference(), it.rt.deepClone());
            for (int i = 0; i < it.mrl.size(); i++) {
                MethodReference mr = (MethodReference) it.mrl.get(i);
                replace(mr, f.createParenthesizedExpression(f.createTypeCast(mr.deepClone(), it.t.deepClone())));
            }
        }
    }

    private static class Item {
        MethodDeclaration md;

        List<MemberReference> mrl;

        TypeReference t;

        TypeReference rt;

        Item(MethodDeclaration md, List<MemberReference> mrl, TypeReference rt, TypeReference t) {
            this.md = md;
            this.mrl = mrl;
            this.rt = rt;
            this.t = t;
        }
    }
}
