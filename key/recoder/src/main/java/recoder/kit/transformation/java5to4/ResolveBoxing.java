package recoder.kit.transformation.java5to4;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.abstraction.*;
import recoder.convenience.TreeWalker;
import recoder.java.*;
import recoder.java.declaration.VariableSpecification;
import recoder.java.expression.Operator;
import recoder.java.expression.ParenthesizedExpression;
import recoder.java.reference.MethodReference;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.TypeReference;
import recoder.kit.MiscKit;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.NameInfo;
import recoder.service.SourceInfo;

import java.util.ArrayList;
import java.util.List;

public class ResolveBoxing extends TwoPassTransformation {
    private final NonTerminalProgramElement root;

    private final List<Expression> toUnbox = new ArrayList<Expression>();

    private final List<Expression> toBox = new ArrayList<Expression>();

    public ResolveBoxing(CrossReferenceServiceConfiguration sc, NonTerminalProgramElement root) {
        super(sc);
        this.root = root;
    }

    public ProblemReport analyze() {
        SourceInfo si = getServiceConfiguration().getSourceInfo();
        TreeWalker tw = new TreeWalker(this.root);
        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            if (pe instanceof Expression) {
                NonTerminalProgramElement parent = pe.getASTParent();
                Expression e = (Expression) pe;
                Type t = si.getType(e);
                Type tt = null;
                if (parent instanceof MethodReference) {
                    MethodReference mr = (MethodReference) parent;
                    Method m = si.getMethod(mr);
                    if (mr.getArguments() != null) {
                        int idx = mr.getArguments().indexOf(e);
                        if (idx != -1)
                            tt = m.getSignature().get(idx);
                    }
                } else if (parent instanceof Operator) {
                    Operator op = (Operator) parent;
                    if (op.getArity() == 2) {
                        Type target = si.getType(op);
                        if (target instanceof PrimitiveType && e instanceof ClassType)
                            tt = target;
                    } else if (op.getArity() == 3) {
                        if (op.getArguments().get(0) != e) {
                            Type target = si.getType(op);
                            if (target instanceof recoder.abstraction.IntersectionType)
                                this.toBox.add(e);
                            if (t instanceof PrimitiveType && target instanceof ClassType)
                                this.toBox.add(e);
                        }
                    }
                } else if (parent instanceof VariableSpecification) {
                    tt = ((VariableSpecification) parent).getType();
                } else if (parent instanceof recoder.java.statement.Return) {
                    tt = si.getType(MiscKit.getParentMemberDeclaration(parent));
                } else if (parent instanceof recoder.java.statement.Switch) {
                    if (t instanceof ClassType && !((ClassType) t).isEnumType())
                        this.toUnbox.add(e);
                } else if (parent instanceof recoder.java.statement.Assert) {
                    if (t instanceof ClassType)
                        this.toUnbox.add(e);
                } else if (parent instanceof recoder.java.reference.ArrayReference) {
                    if (t instanceof ClassType)
                        this.toUnbox.add(e);
                } else if (parent instanceof recoder.java.expression.ArrayInitializer) {
                    tt = ((ArrayType) si.getType((Expression) parent)).getBaseType();
                }
                if (tt != null) {
                    if (tt instanceof ClassType && t instanceof PrimitiveType) {
                        this.toBox.add(e);
                        continue;
                    }
                    if (tt instanceof PrimitiveType && t instanceof ClassType)
                        this.toUnbox.add(e);
                }
            }
        }
        return super.analyze();
    }

    public void transform() {
        super.transform();
        ProgramFactory f = getProgramFactory();
        SourceInfo si = getServiceConfiguration().getSourceInfo();
        NameInfo ni = getServiceConfiguration().getNameInfo();
        for (Expression e : this.toBox) {
            Identifier id;
            PrimitiveType t = (PrimitiveType) si.getType(e);
            if (t == ni.getBooleanType()) {
                id = f.createIdentifier("Boolean");
            } else if (t == ni.getByteType()) {
                id = f.createIdentifier("Byte");
            } else if (t == ni.getShortType()) {
                id = f.createIdentifier("Short");
            } else if (t == ni.getCharType()) {
                id = f.createIdentifier("Character");
            } else if (t == ni.getIntType()) {
                id = f.createIdentifier("Integer");
            } else if (t == ni.getLongType()) {
                id = f.createIdentifier("Long");
            } else if (t == ni.getFloatType()) {
                id = f.createIdentifier("Float");
            } else if (t == ni.getDoubleType()) {
                id = f.createIdentifier("Double");
            } else {
                throw new Error();
            }
            TypeReference tr = f.createTypeReference(id);
            MethodReference replacement = f.createMethodReference(tr, f.createIdentifier("valueOf"), new ASTArrayList(e.deepClone()));
            replace(e, replacement);
        }
        for (Expression e : this.toUnbox) {
            Identifier id;
            ParenthesizedExpression parenthesizedExpression;
            ClassType t = (ClassType) si.getType(e);
            if (t == ni.getJavaLangBoolean()) {
                id = f.createIdentifier("booleanValue");
            } else if (t == ni.getJavaLangByte()) {
                id = f.createIdentifier("byteValue");
            } else if (t == ni.getJavaLangShort()) {
                id = f.createIdentifier("shortValue");
            } else if (t == ni.getJavaLangCharacter()) {
                id = f.createIdentifier("charValue");
            } else if (t == ni.getJavaLangInteger()) {
                id = f.createIdentifier("intValue");
            } else if (t == ni.getJavaLangLong()) {
                id = f.createIdentifier("longValue");
            } else if (t == ni.getJavaLangFloat()) {
                id = f.createIdentifier("floatValue");
            } else if (t == ni.getJavaLangDouble()) {
                id = f.createIdentifier("doubleValue");
            } else {
                throw new Error("cannot unbox type " + t.getFullName() + " (" + t.getClass() + ")");
            }
            if (e instanceof ParenthesizedExpression) {
                parenthesizedExpression = (ParenthesizedExpression) e.deepClone();
            } else {
                parenthesizedExpression = f.createParenthesizedExpression(e.deepClone());
            }
            MethodReference replacement = f.createMethodReference(parenthesizedExpression, id);
            replace(e, replacement);
        }
    }
}
