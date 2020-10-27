package recoder.service;

import recoder.IllegalTransformationException;
import recoder.ModelException;
import recoder.ProgramFactory;
import recoder.ServiceConfiguration;
import recoder.abstraction.Package;
import recoder.abstraction.*;
import recoder.convenience.Format;
import recoder.convenience.Formats;
import recoder.convenience.Naming;
import recoder.convenience.TreeWalker;
import recoder.io.SourceFileRepository;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.expression.Operator;
import recoder.java.expression.operator.New;
import recoder.java.expression.operator.NewArray;
import recoder.java.expression.operator.TypeOperator;
import recoder.java.reference.*;
import recoder.java.statement.*;
import recoder.kit.MiscKit;
import recoder.kit.StatementKit;
import recoder.kit.UnitKit;
import recoder.list.generic.ASTList;
import recoder.util.Debug;
import recoder.util.ProgressListener;
import recoder.util.ProgressListenerManager;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class DefaultSourceInfo extends DefaultProgramModelInfo implements SourceInfo, ChangeHistoryListener, Formats {
    private static final boolean DEBUG = false;
    private static final int CONSTANT_FALSE = 0;
    private static final int CONSTANT_TRUE = 1;
    private static final int NOT_CONSTANT = -1;
    protected final Map<String, Type> name2primitiveType;
    Map<Reference, ProgramModelElement> reference2element = new HashMap<Reference, ProgramModelElement>(1024);
    ProgressListenerManager listeners = new ProgressListenerManager(this);

    public DefaultSourceInfo(ServiceConfiguration config) {
        super(config);
        this.name2primitiveType = new HashMap<String, Type>(64);
    }

    static boolean isPartOf(ProgramElement pe, Class c) {
        NonTerminalProgramElement nonTerminalProgramElement;
        while (pe != null && !c.isInstance(pe))
            nonTerminalProgramElement = pe.getASTParent();
        return (nonTerminalProgramElement != null);
    }

    private static VariableScope findOuterVariableScope(VariableScope ts) {
        NonTerminalProgramElement pe = ts.getASTParent();
        while (pe != null && !(pe instanceof VariableScope))
            pe = pe.getASTParent();
        return (VariableScope) pe;
    }

    private static void addSequentialFollower(Statement s, List<Statement> list) {
        Debug.assertNonnull(s);
        StatementContainer parent = s.getStatementContainer();
        while (true) {
            int c = parent.getStatementCount();
            int p = 0;
            while (parent.getStatementAt(p) != s)
                p++;
            if (p < c - 1) {
                list.add(parent.getStatementAt(p + 1));
                break;
            }
            if (parent instanceof MemberDeclaration) {
                list.add(METHOD_EXIT);
                break;
            }
            if (parent instanceof Statement) {
                if (parent instanceof LoopStatement) {
                    LoopStatement loop = (LoopStatement) parent;
                    list.add(loop);
                    return;
                }
                s = (Statement) parent;
                parent = ((Statement) parent).getStatementContainer();
                continue;
            }
            while (parent instanceof Branch) {
                BranchStatement branchStatement = ((Branch) parent).getParent();
                parent = branchStatement.getStatementContainer();
            }
        }
    }

    private static Statement findInnermostBreakBlock(Statement s) {
        StatementContainer statementContainer = s.getStatementContainer();
        while (statementContainer != null && !(statementContainer instanceof MemberDeclaration)) {
            if (statementContainer instanceof LoopStatement || statementContainer instanceof Switch)
                return (Statement) statementContainer;
            NonTerminalProgramElement nonTerminalProgramElement = statementContainer.getASTParent();
        }
        return null;
    }

    private static LoopStatement findInnermostLoop(Statement s) {
        StatementContainer statementContainer = s.getStatementContainer();
        while (statementContainer != null && !(statementContainer instanceof MemberDeclaration)) {
            if (statementContainer instanceof LoopStatement)
                return (LoopStatement) statementContainer;
            NonTerminalProgramElement nonTerminalProgramElement = statementContainer.getASTParent();
        }
        return null;
    }

    public void initialize(ServiceConfiguration cfg) {
        super.initialize(cfg);
        cfg.getChangeHistory().addChangeHistoryListener(this);
        NameInfo ni = getNameInfo();
        this.name2primitiveType.put("boolean", ni.getBooleanType());
        this.name2primitiveType.put("char", ni.getCharType());
        this.name2primitiveType.put("int", ni.getIntType());
        this.name2primitiveType.put("float", ni.getFloatType());
        this.name2primitiveType.put("double", ni.getDoubleType());
        this.name2primitiveType.put("byte", ni.getByteType());
        this.name2primitiveType.put("short", ni.getShortType());
        this.name2primitiveType.put("long", ni.getLongType());
        this.name2primitiveType.put("boolean[]", ni.createArrayType(ni.getBooleanType()));
        this.name2primitiveType.put("char[]", ni.createArrayType(ni.getCharType()));
        this.name2primitiveType.put("int[]", ni.createArrayType(ni.getIntType()));
        this.name2primitiveType.put("float[]", ni.createArrayType(ni.getFloatType()));
        this.name2primitiveType.put("double[]", ni.createArrayType(ni.getDoubleType()));
        this.name2primitiveType.put("byte[]", ni.createArrayType(ni.getByteType()));
        this.name2primitiveType.put("short[]", ni.createArrayType(ni.getShortType()));
        this.name2primitiveType.put("long[]", ni.createArrayType(ni.getLongType()));
    }

    public void addProgressListener(ProgressListener l) {
        this.listeners.addProgressListener(l);
    }

    public void removeProgressListener(ProgressListener l) {
        this.listeners.removeProgressListener(l);
    }

    protected NameInfo getNameInfo() {
        return super.getNameInfo();
    }

    public void modelChanged(ChangeHistoryEvent changes) {
        List<TreeChange> changed = changes.getChanges();
        int s = changed.size();
        this.listeners.fireProgressEvent(0, s);
        int c = 0;
        int i;
        for (i = 0; i < s; i++) {
            TreeChange tc = changed.get(i);
            if (!tc.isMinor() && tc instanceof DetachChange) {
                processChange(tc);
                this.listeners.fireProgressEvent(++c);
            }
        }
        for (i = 0; i < s; i++) {
            TreeChange tc = changed.get(i);
            if (!tc.isMinor() && tc instanceof AttachChange) {
                processChange(tc);
                this.listeners.fireProgressEvent(++c);
            }
        }
    }

    void processChange(TreeChange change) {
        ProgramElement changed = change.getChangeRoot();
        if (isPartOf(changed, PackageSpecification.class) || isPartOf(changed, Import.class) || determinesGlobalEntityName(changed) || determinesGlobalEntityType(changed)) {
            super.reset();
            this.reference2element.clear();
        }
        if (changed instanceof PackageSpecification) {
            PackageSpecification pkgSpec = (PackageSpecification) changed;
            boolean isAttach = change instanceof AttachChange;
            handleCUPackageChange(pkgSpec.getParent(), Naming.toPathName(pkgSpec.getPackageReference()), isAttach);
        }
        if (changed instanceof PackageReference && isPartOf(changed, PackageSpecification.class))
            System.err.println("WARNING: name info may now contain invalid mappings name2type... (TO BE FIXED)");
        if (changed instanceof Identifier) {
            NonTerminalProgramElement par = changed.getASTParent();
            if (change instanceof AttachChange) {
                register(par);
            } else {
                String oldname = ((Identifier) changed).getText();
                if (par instanceof VariableSpecification) {
                    unregister((VariableSpecification) par, oldname);
                } else if (par instanceof TypeDeclaration) {
                    unregister((TypeDeclaration) par, oldname);
                }
            }
            processIdentifierChanged(change);
        } else if (change instanceof AttachChange) {
            register(changed);
        } else {
            unregister(changed);
        }
    }

    private void handleCUPackageChange(CompilationUnit cu, String originalPkgName, boolean isAttach) {
        DefaultNameInfo dni = (DefaultNameInfo) getNameInfo();
        for (int j = 0, l = cu.getTypeDeclarationCount(); j < l; j++) {
            TypeDeclaration typeDeclaration = cu.getTypeDeclarationAt(j);
            String fullPath = originalPkgName + ("".equals(originalPkgName) ? "" : ".") + typeDeclaration.getName();
            String defaultPkgPath = typeDeclaration.getName();
            if (isAttach) {
                dni.handleTypeRename(typeDeclaration, defaultPkgPath, fullPath);
            } else {
                dni.handleTypeRename(typeDeclaration, fullPath, defaultPkgPath);
            }
        }
    }

    private void processIdentifierChanged(TreeChange tc) {
        if (!(getNameInfo() instanceof DefaultNameInfo))
            return;
        DefaultNameInfo dni = (DefaultNameInfo) getNameInfo();
        Identifier id = (Identifier) tc.getChangeRoot();
        NonTerminalProgramElement npe = id.getParent();
        if (npe instanceof TypeDeclaration) {
            TypeDeclaration td = (TypeDeclaration) npe;
            if (tc instanceof AttachChange) {
                Object old = dni.getType(td.getFullName());
                if (old == null || old == dni.getUnknownType())
                    dni.register(td);
            } else {
                Object old = dni.getType(td.getFullName());
                if (old == td)
                    dni.unregisterClassType(td.getFullName(), true);
            }
        } else if (npe instanceof FieldSpecification) {
            FieldSpecification fs = (FieldSpecification) npe;
            if (tc instanceof AttachChange) {
                dni.register(fs);
            } else {
                dni.unregisterField(fs.getFullName());
            }
        } else if (npe instanceof PackageReference && isPartOf(npe, PackageSpecification.class)) {
            throw new IllegalTransformationException("Changing an Identifier contained in a PackageSpecification is not valid. Change either the containing PackageReference or PackageSpecification instead.");
        }
    }

    private boolean determinesGlobalEntityName(ProgramElement pe) {
        if (pe instanceof Identifier) {
            NonTerminalProgramElement nonTerminalProgramElement = pe.getASTParent();
            return nonTerminalProgramElement instanceof MemberDeclaration;
        }
        return false;
    }

    private boolean determinesGlobalEntityType(ProgramElement pe) {
        return isPartOf(pe, TypeReference.class) && (isPartOf(pe, FieldDeclaration.class) || isPartOf(pe, InheritanceSpecification.class));
    }

    private ProgramElement getDeclaration(ProgramModelElement pme) {
        return (pme instanceof ProgramElement) ? (ProgramElement) pme : null;
    }

    public final TypeDeclaration getTypeDeclaration(ClassType ct) {
        return (ct instanceof TypeDeclaration) ? (TypeDeclaration) ct : null;
    }

    public final MethodDeclaration getMethodDeclaration(Method m) {
        return (m instanceof MethodDeclaration) ? (MethodDeclaration) m : null;
    }

    public final VariableSpecification getVariableSpecification(Variable v) {
        return (v instanceof VariableSpecification) ? (VariableSpecification) v : null;
    }

    public final ConstructorDeclaration getConstructorDeclaration(Constructor c) {
        return (c instanceof ConstructorDeclaration) ? (ConstructorDeclaration) c : null;
    }

    protected ClassType getFromUnitPackage(String name, CompilationUnit cu) {
        String xname = Naming.getPackageName(cu);
        if (xname.length() > 0)
            xname = Naming.dot(xname, name);
        return getNameInfo().getClassType(xname);
    }

    protected ClassType getFromTypeImports(String name, List<Import> il) {
        ClassType result = null;
        NameInfo ni = getNameInfo();
        for (int i = il.size() - 1; i >= 0; i--) {
            Import imp = il.get(i);
            if (!imp.isMultiImport()) {
                TypeReference tr = imp.getTypeReference();
                ClassType newResult = null;
                String trname = imp.isStaticImport() ? imp.getStaticIdentifier().getText() : tr.getName();
                if (name.startsWith(trname)) {
                    int tlen = trname.length();
                    int nlen = name.length();
                    if (tlen == nlen || name.charAt(tlen) == '.') {
                        ReferencePrefix rp = imp.isStaticImport() ? tr : tr.getReferencePrefix();
                        if (rp == null) {
                            trname = name;
                        } else {
                            trname = Naming.toPathName(rp, name);
                        }
                        newResult = ni.getClassType(trname);
                    }
                } else if (name.endsWith(trname) && name.equals(trname = Naming.toPathName(tr))) {
                    newResult = ni.getClassType(trname);
                }
                if (newResult != null && (newResult.isStatic() || !imp.isStaticImport())) {
                    if (result != null && result != newResult)
                        getErrorHandler().reportError(new AmbiguousImportException("Ambiguous import " + Format.toString("%c \"%s\" @%p in %f", imp) + " - could be " + Format.toString("%N", result) + " or " + Format.toString("%N", newResult), imp, result, newResult));
                    result = newResult;
                }
            }
        }
        return result;
    }

    protected ErrorHandler getErrorHandler() {
        return super.getErrorHandler();
    }

    protected ClassType getFromPackageImports(String name, List<Import> il, ClassType searchingFrom) {
        ClassType result = null;
        NameInfo ni = getNameInfo();
        for (int i = il.size() - 1; i >= 0; i--) {
            Import imp = il.get(i);
            if (imp.isMultiImport()) {
                TypeReferenceInfix ref = imp.getReference();
                String xname = Naming.toPathName(ref, name);
                ClassType newResult = ni.getClassType(xname);
                if ((!imp.isStaticImport() && newResult != null && !newResult.isPublic()) || (imp.isStaticImport() && newResult != null && !isVisibleFor(newResult, searchingFrom)))
                    newResult = null;
                if (newResult != null && (newResult.isStatic() || !imp.isStaticImport())) {
                    if (result != null && result != newResult)
                        getErrorHandler().reportError(new AmbiguousImportException("Ambiguous import of type " + name + ": could be " + Format.toString("%N", result) + " or " + Format.toString("%N", newResult), imp, result, newResult));
                    result = newResult;
                }
            }
        }
        return result;
    }

    private ClassType getMemberType(String shortName, ClassType ct) {
        List<? extends ClassType> innerTypes = ct.getTypes();
        for (int i = innerTypes.size() - 1; i >= 0; i--) {
            ClassType candid = innerTypes.get(i);
            if (shortName.equals(candid.getName()))
                return candid;
        }
        List<? extends ClassType> superTypes = ct.getSupertypes();
        for (int j = 0; j < superTypes.size(); j++) {
            ClassType possibleSuperclass = superTypes.get(j);
            ClassType result = getMemberType(shortName, possibleSuperclass);
            if (result != null)
                return result;
        }
        return null;
    }

    protected ClassType getLocalType(String name, TypeScope scope) {
        ClassType result = null;
        int dotPos = name.indexOf('.');
        String shortName = (dotPos == -1) ? name : name.substring(0, dotPos);
        result = scope.getTypeInScope(shortName);
        while (result != null && dotPos != -1) {
            dotPos++;
            int nextDotPos = name.indexOf('.', dotPos);
            shortName = (nextDotPos == -1) ? name.substring(dotPos) : name.substring(dotPos, nextDotPos);
            dotPos = nextDotPos;
            result = getMemberType(shortName, result);
        }
        return result;
    }

    protected ClassType getInheritedType(String name, ClassType ct) {
        int dotPos = name.indexOf('.');
        String shortName = (dotPos == -1) ? name : name.substring(0, dotPos);
        List<ClassType> ctl = getAllTypes(ct);
        ClassType result = null;
        int nc = ctl.size();
        for (int i = 0; i < nc; i++) {
            ClassType c = ctl.get(i);
            if (shortName.equals(c.getName())) {
                result = c;
                break;
            }
        }
        while (result != null && dotPos != -1) {
            dotPos++;
            int nextDotPos = name.indexOf('.', dotPos);
            shortName = (nextDotPos == -1) ? name.substring(dotPos) : name.substring(dotPos, nextDotPos);
            dotPos = nextDotPos;
            result = getMemberType(shortName, result);
        }
        return result;
    }

    public Type getType(String name, ProgramElement context) {
        NonTerminalProgramElement nonTerminalProgramElement1;
        Debug.assertNonnull(name, context);
        NameInfo ni = getNameInfo();
        Type t = this.name2primitiveType.get(name);
        if (t != null)
            return t;
        if (name.equals("void"))
            return null;
        if (name.endsWith("]")) {
            int px = name.indexOf('[');
            Type baseType = getType(name.substring(0, px), context);
            if (baseType == null)
                return null;
            String indexExprs = name.substring(px);
            return ni.getType(baseType.getFullName() + indexExprs);
        }
        updateModel();
        if (context.getASTParent() instanceof InheritanceSpecification)
            nonTerminalProgramElement1 = context.getASTParent().getASTParent().getASTParent();
        NonTerminalProgramElement nonTerminalProgramElement2 = nonTerminalProgramElement1;
        while (nonTerminalProgramElement2 != null && !(nonTerminalProgramElement2 instanceof TypeScope)) {
            nonTerminalProgramElement1 = nonTerminalProgramElement2;
            nonTerminalProgramElement2 = nonTerminalProgramElement2.getASTParent();
        }
        TypeScope scope = (TypeScope) nonTerminalProgramElement2;
        if (scope == null) {
            Debug.log("Null scope during type query " + name + " in context " + Format.toString("%c \"%s\" @%p in %f", nonTerminalProgramElement1));
            Debug.log(Debug.makeStackTrace());
        }
        ClassType result = null;
        TypeScope s = scope;
        while (s != null) {
            result = getLocalType(name, s);
            if (result != null) {
                if (s instanceof StatementBlock) {
                    StatementBlock statementBlock = (StatementBlock) s;
                    for (int i = 0; ; i++) {
                        Statement stmt = statementBlock.getStatementAt(i);
                        if (stmt == result)
                            break;
                        if (stmt == nonTerminalProgramElement1) {
                            result = null;
                            break;
                        }
                    }
                }
                if (result != null)
                    break;
            }
            if (s instanceof TypeDeclaration) {
                TypeDeclaration td = (TypeDeclaration) s;
                ClassType newResult = getInheritedType(name, td);
                if (newResult != null) {
                    if (result == null) {
                        result = newResult;
                        break;
                    }
                    if (result != newResult) {
                        getErrorHandler().reportError(new AmbiguousReferenceException("Type " + Format.toString("%N", newResult) + " is an inherited member type that is also defined as outer member type " + Format.toString("%N", result), null, result, newResult));
                        break;
                    }
                }
            }
            scope = s;
            nonTerminalProgramElement2 = s.getASTParent();
            while (nonTerminalProgramElement2 != null && !(nonTerminalProgramElement2 instanceof TypeScope)) {
                nonTerminalProgramElement1 = nonTerminalProgramElement2;
                nonTerminalProgramElement2 = nonTerminalProgramElement2.getASTParent();
            }
            s = (TypeScope) nonTerminalProgramElement2;
        }
        if (result != null)
            return result;
        CompilationUnit cu = (CompilationUnit) scope;
        ASTList aSTList = cu.getImports();
        if (aSTList != null)
            result = getFromTypeImports(name, (List<Import>) aSTList);
        if (result == null) {
            result = getFromUnitPackage(name, cu);
            if (result == null && aSTList != null)
                result = getFromPackageImports(name, (List<Import>) aSTList, cu.getTypeDeclarationAt(0));
        }
        if (result == null) {
            String defaultName = Naming.dot("java.lang", name);
            result = ni.getClassType(defaultName);
            if (result == null)
                result = ni.getClassType(name);
        }
        if (result != null)
            scope.addTypeToScope(result, name);
        return result;
    }

    public Type getType(TypeReference tr) {
        ParameterizedType parameterizedType = null;
        Type res = (Type) this.reference2element.get(tr);
        if (res != null)
            return res;
        ReferencePrefix rp = tr.getReferencePrefix();
        if (rp instanceof PackageReference) {
            String name = Naming.toPathName(rp, tr.getName());
            ClassType classType = getNameInfo().getClassType(name);
            if (classType != null)
                for (int d = tr.getDimensions(); d > 0; d--) {
                    ArrayType arrayType = getNameInfo().createArrayType(classType);
                }
        } else {
            res = getType(Naming.toPathName(tr), tr);
        }
        if (res == null && !"void".equals(tr.getName())) {
            getErrorHandler().reportError(new UnresolvedReferenceException(Format.toString("Could not resolve %c \"%s\" @%p in %f(14)", tr), tr));
            res = getNameInfo().getUnknownType();
        }
        if (res != null) {
            if (tr.getTypeArguments() != null && tr.getTypeArguments().size() != 0)
                if (res instanceof ArrayType) {
                    res = makeParameterizedArrayType(res, tr.getTypeArguments());
                } else {
                    parameterizedType = new ParameterizedType((ClassType) res, tr.getTypeArguments());
                }
            this.reference2element.put(tr, parameterizedType);
        }
        return parameterizedType;
    }

    public final ClassType getType(TypeDeclaration td) {
        return td;
    }

    public Type getType(VariableSpecification vs) {
        ArrayType arrayType = null;
        if (vs instanceof EnumConstantSpecification)
            return getType((EnumConstantSpecification) vs);
        updateModel();
        TypeReference tr = vs.getParent().getTypeReference();
        Type result = getType(tr);
        if (result != null) {
            int d = vs.getDimensions();
            if (vs.getASTParent() instanceof ParameterDeclaration) {
                ParameterDeclaration pd = (ParameterDeclaration) vs.getASTParent();
                if (pd.isVarArg())
                    d++;
            }
            for (; d > 0; d--)
                arrayType = getNameInfo().createArrayType(result);
        }
        return arrayType;
    }

    private Type getType(EnumConstantSpecification ecs) {
        ClassDeclaration classDeclaration = ecs.getConstructorReference().getClassDeclaration();
        if (classDeclaration != null)
            return classDeclaration;
        return ecs.getParent().getParent();
    }

    public Type getType(ProgramElement pe) {
        ClassType classType = null;
        updateModel();
        Type result = null;
        if (pe instanceof Expression) {
            result = getType((Expression) pe);
        } else if (pe instanceof UncollatedReferenceQualifier) {
            result = getType((UncollatedReferenceQualifier) pe);
        } else if (pe instanceof TypeReference) {
            result = getType((TypeReference) pe);
        } else if (pe instanceof VariableSpecification) {
            result = getType((VariableSpecification) pe);
        } else if (pe instanceof EnumConstantSpecification) {
            result = getType((EnumConstantSpecification) pe);
        } else if (pe instanceof MethodDeclaration) {
            if (!(pe instanceof ConstructorDeclaration))
                result = getReturnType((Method) pe);
        } else if (pe instanceof TypeDeclaration) {
            classType = getType((TypeDeclaration) pe);
        }
        return classType;
    }

    private Type getType(UncollatedReferenceQualifier urq) {
        Reference r = resolveURQ(urq);
        if (r instanceof UncollatedReferenceQualifier)
            return getNameInfo().getUnknownClassType();
        return getType(r);
    }

    public Type getType(Expression expr) {
        Type result = null;
        if (expr instanceof Operator) {
            Operator op = (Operator) expr;
            ASTList<Expression> args = op.getArguments();
            if (op instanceof recoder.java.expression.Assignment) {
                result = getType(args.get(0));
            } else if (op instanceof recoder.java.expression.operator.TypeCast || op instanceof New) {
                result = getType(((TypeOperator) op).getTypeReference());
            } else if (op instanceof NewArray) {
                NewArray n = (NewArray) op;
                TypeReference tr = n.getTypeReference();
                result = getType(tr);
                for (int d = n.getDimensions(); d > 0; d--) {
                    Type oldResult = result;
                    ArrayType arrayType = getNameInfo().getArrayType(result);
                    if (arrayType == null)
                        arrayType = getNameInfo().createArrayType(oldResult);
                }
            } else if (op instanceof recoder.java.expression.operator.PreIncrement || op instanceof recoder.java.expression.operator.PostIncrement || op instanceof recoder.java.expression.operator.PreDecrement || op instanceof recoder.java.expression.operator.PostDecrement || op instanceof recoder.java.expression.ParenthesizedExpression || op instanceof recoder.java.expression.operator.BinaryNot) {
                result = getType(args.get(0));
            } else if (op instanceof recoder.java.expression.operator.Positive || op instanceof recoder.java.expression.operator.Negative) {
                result = getType(args.get(0));
                if (java5Allowed() && result instanceof ClassType) {
                    PrimitiveType primitiveType = getUnboxedType((ClassType) result);
                }
            } else if (op instanceof recoder.java.expression.operator.Plus || op instanceof recoder.java.expression.operator.Minus || op instanceof recoder.java.expression.operator.Times || op instanceof recoder.java.expression.operator.Divide || op instanceof recoder.java.expression.operator.Modulo) {
                PrimitiveType primitiveType1, primitiveType2;
                Type t1 = getType(args.get(0));
                Type t2 = getType(args.get(1));
                if (java5Allowed() && ((t1 instanceof PrimitiveType) ^ (t2 instanceof PrimitiveType) != 0))
                    if (t1 instanceof ClassType) {
                        primitiveType1 = getUnboxedType((ClassType) t1);
                    } else if (t2 instanceof ClassType) {
                        primitiveType2 = getUnboxedType((ClassType) t2);
                    }
                if (op instanceof recoder.java.expression.operator.Plus && (primitiveType1 == getNameInfo().getJavaLangString() || primitiveType2 == getNameInfo().getJavaLangString() || primitiveType1 == null || primitiveType2 == null)) {
                    ClassType classType = getNameInfo().getJavaLangString();
                } else if (primitiveType1 instanceof PrimitiveType && primitiveType2 instanceof PrimitiveType) {
                    PrimitiveType primitiveType = getPromotedType(primitiveType1, primitiveType2);
                    if (primitiveType == null) {
                        getErrorHandler().reportError(new TypingException("Boolean types cannot be promoted in " + op, op));
                        Type type = getNameInfo().getUnknownType();
                    }
                } else if (primitiveType1 != null && primitiveType2 != null) {
                    getErrorHandler().reportError(new TypingException("Illegal operand types for plus " + primitiveType1 + " + " + primitiveType2 + " in expression " + op, op));
                    result = getNameInfo().getUnknownType();
                }
            } else if (op instanceof recoder.java.expression.operator.ShiftRight || op instanceof recoder.java.expression.operator.UnsignedShiftRight || op instanceof recoder.java.expression.operator.ShiftLeft || op instanceof recoder.java.expression.operator.BinaryAnd || op instanceof recoder.java.expression.operator.BinaryOr || op instanceof recoder.java.expression.operator.BinaryXOr) {
                PrimitiveType primitiveType2;
                Type t1 = getType(args.get(0));
                if (java5Allowed()) {
                    Type t2 = getType(args.get(1));
                    if (t1 instanceof ClassType && t2 instanceof PrimitiveType)
                        primitiveType2 = getUnboxedType((ClassType) t1);
                }
                PrimitiveType primitiveType1 = primitiveType2;
            } else if (op instanceof recoder.java.expression.operator.ComparativeOperator || op instanceof recoder.java.expression.operator.LogicalAnd || op instanceof recoder.java.expression.operator.LogicalOr || op instanceof recoder.java.expression.operator.LogicalNot || op instanceof recoder.java.expression.operator.Instanceof) {
                PrimitiveType primitiveType = getNameInfo().getBooleanType();
            } else if (op instanceof recoder.java.expression.operator.Conditional) {
                PrimitiveType primitiveType;
                ClassType classType;
                Expression e1 = args.get(1);
                Expression e2 = args.get(2);
                Type t1 = getType(e1);
                Type t2 = getType(e2);
                if (java5Allowed()) {
                    ClassType classType1;
                    PrimitiveType primitiveType1;
                    if (t1 instanceof PrimitiveType && t2 instanceof ClassType) {
                        PrimitiveType primitiveType2 = getUnboxedType((ClassType) t2);
                        if (primitiveType2 != null) {
                            primitiveType1 = primitiveType2;
                        } else {
                            classType1 = getBoxedType((PrimitiveType) t1);
                        }
                    } else if (classType1 instanceof ClassType && primitiveType1 instanceof PrimitiveType) {
                        PrimitiveType primitiveType2 = getUnboxedType(classType1);
                        if (primitiveType2 != null) {
                            primitiveType = primitiveType2;
                        } else {
                            classType = getBoxedType(primitiveType1);
                        }
                    }
                }
                if (primitiveType == classType) {
                    PrimitiveType primitiveType1 = primitiveType;
                } else if (primitiveType instanceof PrimitiveType && classType instanceof PrimitiveType) {
                    NameInfo ni = getNameInfo();
                    if ((primitiveType == ni.getShortType() && classType == ni.getByteType()) || (classType == ni.getShortType() && primitiveType == ni.getByteType())) {
                        PrimitiveType primitiveType1 = ni.getShortType();
                    } else {
                        result = this.serviceConfiguration.getConstantEvaluator().getCompileTimeConstantType(op);
                        if (result == null) {
                            if (isNarrowingTo(e1, (PrimitiveType) classType))
                                return classType;
                            if (isNarrowingTo(e2, primitiveType))
                                return primitiveType;
                            PrimitiveType primitiveType1 = getPromotedType(primitiveType, (PrimitiveType) classType);
                        }
                    }
                } else if (primitiveType instanceof PrimitiveType || classType instanceof PrimitiveType) {
                    getErrorHandler().reportError(new TypingException("Incompatible types in conditional", op));
                    result = getNameInfo().getUnknownType();
                } else if (primitiveType == getNameInfo().getNullType()) {
                    ClassType classType1 = classType;
                } else if (classType == getNameInfo().getNullType()) {
                    PrimitiveType primitiveType1 = primitiveType;
                } else if (isWidening(primitiveType, classType)) {
                    ClassType classType1 = classType;
                } else if (isWidening(classType, primitiveType)) {
                    PrimitiveType primitiveType1 = primitiveType;
                } else if (java5Allowed() && primitiveType instanceof ClassType && classType instanceof ClassType) {
                    List<Type> tml = new ArrayList<Type>();
                    tml.addAll(getAllSupertypes((ClassType) primitiveType));
                    List<? extends ClassType> comp = getAllSupertypes(classType);
                    for (int j = tml.size() - 1; j >= 0; j--) {
                        if (comp.indexOf(tml.get(j)) == -1)
                            tml.remove(j);
                    }
                    removeSupertypesFromList(tml);
                    if (tml.size() == 0)
                        throw new Error();
                    if (tml.size() == 1) {
                        result = tml.get(0);
                    } else {
                        IntersectionType intersectionType = new IntersectionType(tml, this);
                    }
                } else {
                    getErrorHandler().reportError(new TypingException("Incompatible types in conditional", op));
                    result = getNameInfo().getUnknownType();
                }
            } else {
                Debug.error("Type resolution not implemented for operation " + op.getClass().getName());
            }
        } else if (expr instanceof recoder.java.expression.Literal) {
            if (expr instanceof recoder.java.expression.literal.NullLiteral) {
                ClassType classType = getNameInfo().getNullType();
            } else if (expr instanceof recoder.java.expression.literal.BooleanLiteral) {
                PrimitiveType primitiveType = getNameInfo().getBooleanType();
            } else if (expr instanceof recoder.java.expression.literal.LongLiteral) {
                PrimitiveType primitiveType = getNameInfo().getLongType();
            } else if (expr instanceof recoder.java.expression.literal.IntLiteral) {
                PrimitiveType primitiveType = getNameInfo().getIntType();
            } else if (expr instanceof recoder.java.expression.literal.FloatLiteral) {
                PrimitiveType primitiveType = getNameInfo().getFloatType();
            } else if (expr instanceof recoder.java.expression.literal.DoubleLiteral) {
                PrimitiveType primitiveType = getNameInfo().getDoubleType();
            } else if (expr instanceof recoder.java.expression.literal.CharLiteral) {
                PrimitiveType primitiveType = getNameInfo().getCharType();
            } else if (expr instanceof recoder.java.expression.literal.StringLiteral) {
                ClassType classType = getNameInfo().getJavaLangString();
            }
        } else if (expr instanceof Reference) {
            if (expr instanceof UncollatedReferenceQualifier) {
                result = getType((UncollatedReferenceQualifier) expr);
            } else if (expr instanceof recoder.java.reference.MetaClassReference) {
                ClassType classType = getNameInfo().getJavaLangClass();
            } else if (expr instanceof VariableReference) {
                Variable v = getVariable((VariableReference) expr);
                if (v != null) {
                    result = v.getType();
                    if (expr instanceof FieldReference) {
                        Type t = getType(((FieldReference) expr).getReferencePrefix());
                        if (t instanceof ParameterizedType && containsTypeParameter(result))
                            result = (replaceTypeParameter((ParameterizedType) t, result)).baseType;
                        if (t instanceof ClassType && containsTypeParameter(result)) {
                            List<? extends ClassType> allSupertypes = ((ClassType) t).getAllSupertypes();
                            for (int i = 1; i < allSupertypes.size(); i++) {
                                ClassType st = allSupertypes.get(i);
                                if (st instanceof ParameterizedType) {
                                    result = (replaceTypeParameter((ParameterizedType) st, result)).baseType;
                                    if (!containsTypeParameter(result))
                                        break;
                                }
                            }
                        }
                    }
                } else {
                    getErrorHandler().reportError(new UnresolvedReferenceException(Format.toString("Could not resolve %c \"%s\" @%p in %f", expr) + " (01)", expr));
                    Field field = getNameInfo().getUnknownField();
                }
            } else if (expr instanceof MethodReference) {
                Method m = getMethod((MethodReference) expr);
                if (m != null) {
                    ParameterizedType parameterizedType = null;
                    result = m.getReturnType();
                    if (containsTypeParameter(result) && m.getTypeParameters() != null && m.getTypeParameters().size() != 0)
                        for (int i = 0; i < m.getTypeParameters().size(); i++) {
                            ClassType classType = null;
                            Type type1 = null;
                            TypeParameter currentTypeParam = m.getTypeParameters().get(i);
                            MethodReference methodReference = (MethodReference) expr;
                            Type replacement = null;
                            if (methodReference.getTypeArguments() != null) {
                                TypeArgumentDeclaration ta = methodReference.getTypeArguments().get(i);
                                replacement = getType(ta.getTypeReferenceAt(0));
                                if (ta.getTypeArguments() != null) {
                                    ParameterizedType parameterizedType1 = new ParameterizedType((ClassType) replacement, replaceTypeParameter(ta.getTypeArguments(), currentTypeParam, (ClassType) replacement));
                                }
                            } else {
                                replacement = inferType(m, methodReference, currentTypeParam.getName());
                            }
                            List<? extends TypeArgument> typeArgs = null;
                            if (result instanceof ParameterizedType) {
                                typeArgs = ((ParameterizedType) result).getTypeArgs();
                                typeArgs = replaceTypeParameter(typeArgs, currentTypeParam, (ClassType) replacement);
                                classType = ((ParameterizedType) result).getGenericType();
                            }
                            if (classType == currentTypeParam)
                                type1 = replacement;
                            if (typeArgs != null)
                                parameterizedType = new ParameterizedType((ClassType) type1, typeArgs);
                        }
                    MethodReference mr = (MethodReference) expr;
                    if (mr.getReferencePrefix() != null) {
                        Type type1 = null, t = getType(mr.getReferencePrefix());
                        if (t instanceof ParameterizedType && containsTypeParameter(parameterizedType))
                            type1 = (replaceTypeParameter((ParameterizedType) t, parameterizedType)).baseType;
                        if (t instanceof ClassType && containsTypeParameter(type1)) {
                            List<? extends ClassType> allSupertypes = ((ClassType) t).getAllSupertypes();
                            for (int i = 1; i < allSupertypes.size(); i++) {
                                ClassType st = allSupertypes.get(i);
                                if (st instanceof ParameterizedType) {
                                    type1 = (replaceTypeParameter((ParameterizedType) st, type1)).baseType;
                                    if (!containsTypeParameter(type1))
                                        break;
                                }
                            }
                        }
                    }
                }
            } else if (expr instanceof AnnotationPropertyReference) {
                AnnotationProperty ap = getAnnotationProperty((AnnotationPropertyReference) expr);
                if (ap != null)
                    result = ap.getReturnType();
            } else if (expr instanceof ArrayLengthReference) {
                PrimitiveType primitiveType = getNameInfo().getIntType();
            } else if (expr instanceof ArrayReference) {
                ArrayReference aref = (ArrayReference) expr;
                Type ht = getType(aref.getReferencePrefix());
                if (ht != null && !(ht instanceof DefaultNameInfo.UnknownClassType)) {
                    ASTList aSTList = aref.getDimensionExpressions();
                    int dims = aSTList.size();
                    for (int i = 0; i < dims; i++)
                        ht = ((ArrayType) ht).getBaseType();
                    if (ht != null) {
                        result = ht;
                    } else {
                        getErrorHandler().reportError(new TypingException("Not an array type: " + ht + " in expression " + expr, expr));
                        result = getNameInfo().getUnknownType();
                    }
                }
            } else if (expr instanceof ThisReference) {
                ReferencePrefix rp = ((ThisReference) expr).getReferencePrefix();
                if (rp == null) {
                    ClassType classType = getContainingClassType(expr);
                } else {
                    result = getType(rp);
                }
            } else if (expr instanceof SuperReference) {
                ClassType thisType;
                ReferencePrefix rp = ((SuperReference) expr).getReferencePrefix();
                if (rp == null) {
                    thisType = getContainingClassType(expr);
                } else {
                    thisType = (ClassType) getType(rp);
                }
                List<ClassType> supers = thisType.getSupertypes();
                if (supers != null && !supers.isEmpty())
                    result = supers.get(0);
            }
        } else if (expr instanceof recoder.java.expression.ArrayInitializer) {
            NonTerminalProgramElement nonTerminalProgramElement = null;
            Expression expression = expr;
            while (expression != null && !(expression instanceof VariableSpecification) && !(expression instanceof NewArray))
                nonTerminalProgramElement = expression.getASTParent();
            result = getType(nonTerminalProgramElement);
        } else if (expr instanceof recoder.java.expression.ElementValueArrayInitializer) {
            NonTerminalProgramElement nonTerminalProgramElement = null;
            Expression expression = expr;
            while (expression != null && !(expression instanceof VariableSpecification))
                nonTerminalProgramElement = expression.getASTParent();
            result = getType(nonTerminalProgramElement);
        } else if (expr instanceof AnnotationUseSpecification) {
            result = getType(((AnnotationUseSpecification) expr).getTypeReference());
        } else {
            Debug.error("Type analysis for general expressions is currently not implemented: " + expr + " <" + expr.getClass().getName() + ">");
        }
        return result;
    }

    private Type inferType(Method m, MethodReference mr, String typeParamName) {
        List<Type> result = new ArrayList<Type>();
        List<Type> sig = m.getSignature();
        for (int j = 0; j < sig.size(); j++) {
            Type t = sig.get(j);
            Expression e = mr.getArguments().get(j);
            Type actualArgType = getType(e);
            inferType1(typeParamName, result, t, actualArgType);
        }
        removeSupertypesFromList(result);
        if (result.size() == 0)
            return getNameInfo().getJavaLangObject();
        if (result.size() == 1)
            return result.get(0);
        return new IntersectionType(result, getServiceConfiguration().getImplicitElementInfo());
    }

    private void removeSupertypesFromList(List<Type> result) {
        for (int j = result.size() - 1; j >= 0; j--) {
            for (int k = 0; k < result.size() - 1; k++) {
                Type a = result.get(j);
                Type b = result.get(k);
                if (a instanceof ArrayType) {
                    assert b instanceof ArrayType;
                    while (a instanceof ArrayType) {
                        a = ((ArrayType) a).getBaseType();
                        b = ((ArrayType) b).getBaseType();
                    }
                }
                if (isSupertype((ClassType) a, (ClassType) b)) {
                    result.remove(j);
                    break;
                }
            }
        }
    }

    private void inferType1(String typeParamName, List<Type> result, Type t, Type actualArgType) {
        inferType2(typeParamName, result, t, actualArgType);
        if (t instanceof ParameterizedType && actualArgType instanceof ParameterizedType) {
            ParameterizedType tp = (ParameterizedType) t;
            ParameterizedType ap = (ParameterizedType) actualArgType;
            for (int i = 0; i < tp.getTypeArgs().size(); i++)
                inferType1(typeParamName, result, getBaseType(tp.getTypeArgs().get(i)), getBaseType(ap.getTypeArgs().get(i)));
        }
    }

    private void inferType2(String typeParamName, List<Type> result, Type t, Type actualArgType) {
        Type toAdd = actualArgType;
        int reduceDim = 0;
        while (t instanceof ArrayType) {
            t = ((ArrayType) t).getBaseType();
            reduceDim++;
        }
        if (t instanceof TypeParameter && t.getName().equals(typeParamName)) {
            while (reduceDim > 0) {
                toAdd = ((ArrayType) toAdd).getBaseType();
                reduceDim--;
            }
            List<? extends Type> ctl = new ArrayList<Type>();
            int dim = 0;
            if (toAdd instanceof ArrayType) {
                while (toAdd instanceof ArrayType) {
                    toAdd = ((ArrayType) toAdd).getBaseType();
                    dim++;
                }
                ctl = getAllSupertypes((ClassType) toAdd);
                List<Type> tmp = new ArrayList<Type>(ctl.size());
                for (int i = 0; i < ctl.size(); i++)
                    tmp.add(getNameInfo().createArrayType(ctl.get(i), dim));
                ctl = tmp;
            } else {
                ctl = getAllSupertypes((ClassType) toAdd);
            }
            if (result.isEmpty()) {
                result.addAll(ctl);
            } else {
                for (int i = result.size() - 1; i >= 0; i--) {
                    if (ctl.indexOf(result.get(i)) == -1)
                        result.remove(i);
                }
            }
        }
    }

    private List<TypeArgument> replaceTypeParameter(List<? extends TypeArgument> typeArgs, TypeParameter typeParam, ClassType replacement) {
        List<TypeArgument> res = new ArrayList<TypeArgument>();
        for (int i = 0; i < typeArgs.size(); i++) {
            TypeArgument ta = typeArgs.get(i);
            TypeArgument newTa = ta;
            List<? extends TypeArgument> newTas = null;
            if (ta.getTypeArguments() != null)
                newTas = replaceTypeParameter(ta.getTypeArguments(), typeParam, replacement);
            if (getBaseType(ta) == typeParam) {
                newTa = new DefaultProgramModelInfo.ResolvedTypeArgument(ta.getWildcardMode(), replacement, newTas);
            } else if (newTas != null) {
                newTa = new DefaultProgramModelInfo.ResolvedTypeArgument(ta.getWildcardMode(), getBaseType(ta), newTas);
            }
            res.add(newTa);
        }
        return res;
    }

    public boolean containsTypeParameter(Type t) {
        while (t instanceof ArrayType)
            t = ((ArrayType) t).getBaseType();
        if (!(t instanceof ClassType))
            return false;
        if (t instanceof TypeParameter)
            return true;
        if (t instanceof ParameterizedType) {
            ParameterizedType pt = (ParameterizedType) t;
            if (pt.getGenericType() instanceof TypeParameter)
                return true;
            for (TypeArgument ta : pt.getTypeArgs()) {
                if (containsTypeParameter(ta))
                    return true;
            }
        }
        return false;
    }

    private boolean containsTypeParameter(TypeArgument ta) {
        if (getBaseType(ta) instanceof TypeParameter)
            return true;
        if (ta.getTypeArguments() != null)
            for (TypeArgument nta : ta.getTypeArguments()) {
                if (containsTypeParameter(nta))
                    return true;
            }
        return false;
    }

    private List<? extends TypeArgument> replaceTypeArgsRec(ParameterizedType context, List<? extends TypeArgument> targs) {
        List<TypeArgument> result = new ArrayList<TypeArgument>(targs.size());
        for (TypeArgument ta : targs) {
            Type ct = getBaseType(ta);
            DefaultProgramModelInfo.ReplaceTypeArgResult repl = replaceTypeParameter(context, ct);
            result.add(new DefaultProgramModelInfo.ResolvedTypeArgument(repl.wildcardMode, repl.baseType, (repl.baseType instanceof ParameterizedType) ? ((ParameterizedType) repl.baseType).getTypeArgs() : null));
        }
        return result;
    }

    private DefaultProgramModelInfo.ReplaceTypeArgResult replaceTypeParameter(ParameterizedType context, Type toReplace) {
        ClassType classType;
        List<? extends TypeArgument> newTypeArgs = null;
        if (toReplace instanceof ArrayType) {
            ArrayType arrayType = (ArrayType) toReplace;
            DefaultProgramModelInfo.ReplaceTypeArgResult innerResult = replaceTypeParameter(context, arrayType.getBaseType());
            DefaultProgramModelInfo.ReplaceTypeArgResult replaceTypeArgResult1 = new DefaultProgramModelInfo.ReplaceTypeArgResult(getNameInfo().createArrayType(innerResult.baseType), null);
            return replaceTypeArgResult1;
        }
        if (toReplace instanceof ParameterizedType) {
            ParameterizedType pt = (ParameterizedType) toReplace;
            newTypeArgs = replaceTypeArgsRec(context, pt.getTypeArgs());
            classType = pt.getGenericType();
        }
        DefaultProgramModelInfo.ReplaceTypeArgResult result = new DefaultProgramModelInfo.ReplaceTypeArgResult(classType, null);
        if (classType instanceof TypeParameter)
            result = replaceTypeArg(classType, context.getTypeArgs(), context.getGenericType().getTypeParameters());
        if (newTypeArgs != null)
            result = new DefaultProgramModelInfo.ReplaceTypeArgResult(new ParameterizedType((ClassType) result.baseType, newTypeArgs), result.wildcardMode);
        return result;
    }

    public boolean isNarrowingTo(Expression expr, PrimitiveType to) {
        int minValue, maxValue;
        NameInfo ni = getNameInfo();
        if (to == ni.getByteType()) {
            minValue = -128;
            maxValue = 127;
        } else if (to == ni.getCharType()) {
            minValue = 0;
            maxValue = 65535;
        } else if (to == ni.getShortType()) {
            minValue = -32768;
            maxValue = 32767;
        } else {
            return false;
        }
        ConstantEvaluator ce = this.serviceConfiguration.getConstantEvaluator();
        ConstantEvaluator.EvaluationResult res = new ConstantEvaluator.EvaluationResult();
        if (!ce.isCompileTimeConstant(expr, res) || res.getTypeCode() != 4)
            return false;
        int value = res.getInt();
        return (minValue <= value && value <= maxValue);
    }

    public Type getType(ProgramModelElement pme) {
        Debug.assertNonnull(pme);
        Type result = null;
        if (pme instanceof Type) {
            result = (Type) pme;
        } else if (pme instanceof ProgramElement) {
            result = getType((ProgramElement) pme);
            if (result == null && pme instanceof VariableSpecification) {
                if (pme instanceof EnumConstantSpecification)
                    throw new IllegalStateException("Enum constant outside an enum, this shouldn't even be possible");
                getErrorHandler().reportError(new UnresolvedReferenceException(Format.toString("Unknown type of %c \"%s\" @%p in %f", pme), ((VariableSpecification) pme).getParent().getTypeReference()));
                result = getNameInfo().getUnknownType();
            }
            if (result == null && pme instanceof EnumConstantDeclaration)
                throw new Error("fatal error: EnumConstantDeclaration occured outside enum declaration");
        } else {
            result = pme.getProgramModelInfo().getType(pme);
        }
        return result;
    }

    public ClassType getContainingClassType(ProgramElement context) {
        NonTerminalProgramElement nonTerminalProgramElement;
        Debug.assertNonnull(context);
        if (context instanceof TypeDeclaration)
            nonTerminalProgramElement = context.getASTParent();
        while (true) {
            if (nonTerminalProgramElement instanceof ClassType)
                return (ClassType) nonTerminalProgramElement;
            nonTerminalProgramElement = nonTerminalProgramElement.getASTParent();
            if (nonTerminalProgramElement == null)
                return null;
        }
    }

    public ClassType getContainingClassType(Member m) {
        Debug.assertNonnull(m);
        ClassType result = null;
        ProgramElement pe = getDeclaration(m);
        if (pe == null) {
            result = m.getProgramModelInfo().getContainingClassType(m);
        } else {
            result = getContainingClassType(pe);
        }
        return result;
    }

    protected Field getInheritedField(String name, ClassType ct) {
        List<? extends Field> fl = ct.getAllFields();
        int nf = fl.size();
        for (int i = 0; i < nf; i++) {
            Field f = fl.get(i);
            if (name.equals(f.getName()))
                return f;
        }
        return null;
    }

    public Variable getVariable(String name, ProgramElement context) {
        NonTerminalProgramElement nonTerminalProgramElement1, nonTerminalProgramElement2;
        Field field;
        Variable variable;
        ProgramElement originalContext = context;
        Debug.assertNonnull(name, context);
        updateModel();
        if (java5Allowed() && (context instanceof VariableReference || context instanceof UncollatedReferenceQualifier) && context.getASTParent() instanceof Case && getType(((Case) context.getASTParent()).getParent().getExpression()) instanceof EnumDeclaration) {
            EnumConstantSpecification ecs = (EnumConstantSpecification) ((EnumDeclaration) getType(((Case) context.getASTParent()).getParent().getExpression())).getVariableInScope(name);
            if (ecs != null)
                return ecs;
            return null;
        }
        ProgramElement pe = context;
        while (pe != null && !(pe instanceof VariableScope)) {
            context = pe;
            nonTerminalProgramElement2 = pe.getASTParent();
        }
        if (nonTerminalProgramElement2 == null)
            return null;
        VariableScope scope = (VariableScope) nonTerminalProgramElement2;
        do {
            VariableSpecification variableSpecification = scope.getVariableInScope(name);
            if (variableSpecification != null) {
                if (scope instanceof StatementBlock) {
                    StatementBlock statementBlock = (StatementBlock) scope;
                    VariableDeclaration def = variableSpecification.getParent();
                    for (int i = 0; ; i++) {
                        Statement s = statementBlock.getStatementAt(i);
                        if (s == def)
                            break;
                        if (s == context) {
                            variableSpecification = null;
                            break;
                        }
                    }
                }
                if (variableSpecification != null)
                    break;
            }
            if (scope instanceof TypeDeclaration) {
                field = getInheritedField(name, (ClassType) scope);
                if (field != null)
                    break;
            }
            nonTerminalProgramElement2 = scope.getASTParent();
            while (nonTerminalProgramElement2 != null && !(nonTerminalProgramElement2 instanceof VariableScope)) {
                nonTerminalProgramElement1 = nonTerminalProgramElement2;
                nonTerminalProgramElement2 = nonTerminalProgramElement2.getASTParent();
            }
            scope = (VariableScope) nonTerminalProgramElement2;
        } while (scope != null);
        if (field == null && java5Allowed()) {
            ASTList aSTList = UnitKit.getCompilationUnit(nonTerminalProgramElement1).getImports();
            TypeDeclaration typeDeclaration = MiscKit.getParentTypeDeclaration(originalContext);
            variable = getVariableFromStaticSingleImport(name, (List<Import>) aSTList, typeDeclaration);
            if (variable == null)
                variable = getVariableFromStaticOnDemandImport(name, (List<Import>) aSTList, typeDeclaration);
        }
        return variable;
    }

    private Variable getVariableFromStaticSingleImport(String name, List<Import> imports, ClassType context) {
        Field field;
        Variable result = null;
        Variable oldResult = null;
        Import firstImport = null;
        for (int i = 0, max = imports.size(); i < max; i++) {
            Import imp = imports.get(i);
            if (imp.isStaticImport() && !imp.isMultiImport())
                if (name.equals(imp.getStaticIdentifier().getText())) {
                    List<? extends Field> fields = getFields((ClassType) getType(imp.getTypeReference()));
                    for (int f = 0, maxF = fields.size(); f < maxF; f++) {
                        Field field1 = fields.get(f);
                        if (field1.getName().equals(name) &&
                                isVisibleFor(field1, context)) {
                            field = field1;
                            if (oldResult != null && oldResult != field)
                                getErrorHandler().reportError(new AmbiguousStaticFieldImportException(firstImport, imp, oldResult, field));
                            firstImport = imp;
                            Field field2 = field1;
                            break;
                        }
                    }
                }
        }
        return field;
    }

    private Variable getVariableFromStaticOnDemandImport(String name, List<Import> imports, ClassType context) {
        Field field;
        Debug.assertNonnull(name);
        Debug.assertNonnull(imports);
        Debug.assertNonnull(context);
        Variable result = null;
        Variable oldResult = null;
        Import firstImport = null;
        for (int i = 0, max = imports.size(); i < max; i++) {
            Import imp = imports.get(i);
            if (imp.isStaticImport() && imp.isMultiImport()) {
                List<? extends Field> fields = getFields((ClassType) getType(imp.getTypeReference()));
                for (int f = 0, maxF = fields.size(); f < maxF; f++) {
                    Field field1 = fields.get(f);
                    if (field1.getName().equals(name) &&
                            isVisibleFor(field1, context)) {
                        field = field1;
                        if (oldResult != null && oldResult != field)
                            getErrorHandler().reportError(new AmbiguousStaticFieldImportException(firstImport, imp, oldResult, field));
                        firstImport = imp;
                        Field field2 = field1;
                        break;
                    }
                }
            }
        }
        return field;
    }

    public final Variable getVariable(VariableSpecification vs) {
        return vs;
    }

    public Field getField(FieldReference fr) {
        Field res = (Field) this.reference2element.get(fr);
        if (res != null)
            return res;
        updateModel();
        String name = fr.getName();
        ReferencePrefix rp = fr.getReferencePrefix();
        if (rp == null) {
            res = (Field) getVariable(name, fr);
            if (res != null)
                this.reference2element.put(fr, res);
            return res;
        }
        ClassType thisType = getContainingClassType(fr);
        if (thisType == null)
            return null;
        ClassType ct = (ClassType) getType(rp);
        if (ct == null || ct instanceof DefaultNameInfo.UnknownClassType)
            return null;
        List<? extends Field> fl = ct.getAllFields();
        if (fl == null)
            return null;
        for (int i = fl.size() - 1; i >= 0; i--) {
            res = fl.get(i);
            if (res.getName() == name) {
                this.reference2element.put(fr, res);
                return res;
            }
        }
        return null;
    }

    public Variable getVariable(VariableReference vr) {
        if (vr instanceof FieldReference)
            return getField((FieldReference) vr);
        Variable res = (Variable) this.reference2element.get(vr);
        if (res != null)
            return res;
        res = getVariable(vr.getName(), vr);
        if (res != null)
            this.reference2element.put(vr, res);
        return res;
    }

    public List<Type> makeSignature(List<Expression> args) {
        if (args == null || args.isEmpty())
            return new ArrayList<Type>(0);
        int arity = args.size();
        List<Type> result = new ArrayList<Type>(arity);
        for (int i = 0; i < arity; i++) {
            Expression e = args.get(i);
            Type et = getType(e);
            if (et == null) {
                getErrorHandler().reportError(new TypingException("Unknown type for argument #" + i + " in call " + Format.toString("%c \"%s\" @%p in %f", e.getExpressionContainer()), e));
                et = getNameInfo().getUnknownType();
            }
            result.add(et);
        }
        return result;
    }

    public final Method getMethod(MethodDeclaration md) {
        return md;
    }

    public final Constructor getConstructor(ConstructorDeclaration cd) {
        return cd;
    }

    private final String isAppropriate(Method m, MethodReference mr) {
        if (mr.getReferencePrefix() == null)
            return (m.isStatic() || !occursInStaticContext(mr)) ? null : "method invocation to non-static method occurs in static context (a)";
        if (mr.getReferencePrefix() instanceof TypeReference && !m.isStatic())
            return "Static access to a non-static member";
        if (mr.getTypeReferenceCount() == 1)
            return null;
        if (mr.getReferencePrefix() instanceof SuperReference) {
            SuperReference sr = (SuperReference) mr.getReferencePrefix();
            if (m.isAbstract()) ;
            if (occursInStaticContext(mr))
                return "method invocation to non-static method occurs in static context (c)";
            if (sr.getReferencePrefix() == null || sr.getReferencePrefix() instanceof TypeReference) ;
            return null;
        }
        if (mr.getReferenceSuffix() != null && m.getReturnType() == null)
            return "void method must not have a reference suffix";
        return null;
    }

    private final boolean occursInStaticContext(MethodReference mr) {
        NonTerminalProgramElement nonTerminalProgramElement;
        MethodReference methodReference = mr;
        while (methodReference != null) {
            if (methodReference instanceof ClassInitializer)
                return ((ClassInitializer) methodReference).isStatic();
            if (methodReference instanceof MethodDeclaration)
                return ((MethodDeclaration) methodReference).isStatic();
            if (methodReference instanceof FieldDeclaration)
                return ((FieldDeclaration) methodReference).isStatic();
            nonTerminalProgramElement = methodReference.getASTParent();
        }
        getErrorHandler().reportError(new ModelException("cannot determine if MethodReference " + Format.toString(nonTerminalProgramElement) + " occurs in static context; check parent links!"));
        return false;
    }

    public AnnotationProperty getAnnotationProperty(AnnotationPropertyReference apr) {
        AnnotationProperty res = (AnnotationProperty) this.reference2element.get(apr);
        if (res != null)
            return res;
        Type at = getType(apr.getParent().getParent().getTypeReference());
        if (at instanceof ClassType && ((ClassType) at).isAnnotationType()) {
            ClassType ct = (ClassType) at;
            List<? extends Method> ml = ct.getMethods();
            for (int i = 0; i < ml.size(); i++) {
                if (ml.get(i).getName().equals(apr.getIdentifier().getText())) {
                    res = (AnnotationProperty) ml.get(i);
                    break;
                }
            }
            if (res == null) {
                getErrorHandler().reportError(new UnresolvedReferenceException(Format.toString("Could not resolve %c \"%s\" @%p in %f (12)", apr), apr));
                res = getNameInfo().getUnknownAnnotationProperty();
            }
        } else if (at == null) {
            getErrorHandler().reportError(new UnresolvedReferenceException(Format.toString("Could not resolve %c \"%s\" @%p in %f (13)", apr), apr));
        } else {
            getErrorHandler().reportError(new ModelException(Format.toString("%c \"%s\" @%p in %f does not reference an annotation type!", apr)));
            res = getNameInfo().getUnknownAnnotationProperty();
        }
        this.reference2element.put(apr, res);
        return res;
    }

    public Method getMethod(MethodReference mr) {
        Method res = (Method) this.reference2element.get(mr);
        if (res != null)
            return res;
        List<? extends Method> mlist = getMethods(mr);
        if (mlist == null || mlist.isEmpty()) {
            getErrorHandler().reportError(new UnresolvedReferenceException(Format.toString("Could not resolve %c \"%s\" @%p in %f (02)", mr), mr));
            return getNameInfo().getUnknownMethod();
        }
        if (mlist.size() > 1) {
            getErrorHandler().reportError(new AmbiguousReferenceException(Format.toString("%c \"%s\" @%p in %f is ambiguous - it could be one of ", mr) + Format.toString("%N", mlist), mr, mlist));
        } else {
            String msg;
            if ((msg = isAppropriate(mlist.get(0), mr)) != null)
                getErrorHandler().reportError(new UnresolvedReferenceException(Format.toString("Inappropriate method access: " + msg + " at " + "%c \"%s\" @%p in %f", mr), mr));
        }
        res = mlist.get(0);
        this.reference2element.put(mr, res);
        return res;
    }

    public List<Method> getMethods(MethodReference mr) {
        Debug.assertNonnull(mr);
        updateModel();
        List<Method> result = null;
        List<Type> signature = makeSignature(mr.getArguments());
        ReferencePrefix rp = mr.getReferencePrefix();
        if (rp == null) {
            ClassType targetClass = getContainingClassType(mr);
            result = getMethods(targetClass, mr.getName(), signature, mr.getTypeArguments());
            if (result != null && result.size() > 0)
                return result;
            for (ClassTypeContainer ctc = targetClass.getContainer(); ctc != null; ctc = ctc.getContainer()) {
                if (ctc instanceof ClassType) {
                    result = getMethods((ClassType) ctc, mr.getName(), signature, mr.getTypeArguments());
                    if (result != null && result.size() > 0)
                        return result;
                }
            }
            if (java5Allowed()) {
                ASTList aSTList = UnitKit.getCompilationUnit(mr).getImports();
                result = getMethodsFromStaticSingleImports(mr, (List<Import>) aSTList);
                if (result != null && result.size() > 0)
                    return result;
                result = getMethodsFromStaticOnDemandImports(mr, (List<Import>) aSTList);
                if (result != null && result.size() > 0)
                    return result;
            }
            getErrorHandler().reportError(new UnresolvedReferenceException(Format.toString("Could not resolve %c \"%s\" @%p in %f (03)", mr), mr));
            List<Method> list = new ArrayList<Method>(1);
            list.add(getNameInfo().getUnknownMethod());
            result = list;
        } else {
            ClassType classType;
            Type rpt = getType(rp);
            if (rpt == null) {
                getErrorHandler().reportError(new UnresolvedReferenceException(Format.toString("Could not resolve %c \"%s\" @%p in %f (04)", rp), rp));
                List<Method> list = new ArrayList<Method>(1);
                list.add(getNameInfo().getUnknownMethod());
                return list;
            }
            if (rpt instanceof ArrayType)
                classType = getNameInfo().getJavaLangObject();
            result = getMethods(classType, mr.getName(), signature, mr.getTypeArguments());
        }
        return result;
    }

    private List<Method> getMethodsFromStaticOnDemandImports(MethodReference mr, List<Import> imports) {
        NameInfo ni = getNameInfo();
        List<Method> result = new ArrayList<Method>();
        for (int i = 0, max = imports.size(); i < max; i++) {
            Import imp = imports.get(i);
            if (imp.isStaticImport() && imp.isMultiImport()) {
                List<? extends Method> ml = ni.getClassType(Naming.toPathName(imp.getTypeReference())).getMethods();
                for (int j = 0; j < ml.size(); j++) {
                    Method m = ml.get(j);
                    if (m.isStatic() && m.getName().equals(mr.getName()))
                        result.add(m);
                }
            }
        }
        List<Type> sig = makeSignature(mr.getArguments());
        return doThreePhaseFilter(result, sig, mr.getName(), MiscKit.getParentTypeDeclaration(mr), mr.getTypeArguments());
    }

    private List<Method> getMethodsFromStaticSingleImports(MethodReference mr, List<Import> imports) {
        NameInfo ni = getNameInfo();
        List<Method> result = new ArrayList<Method>();
        for (int i = 0, max = imports.size(); i < max; i++) {
            Import imp = imports.get(i);
            if (imp.isStaticImport() && !imp.isMultiImport())
                if (imp.getStaticIdentifier().getText().equals(mr.getName())) {
                    List<? extends Method> ml = ni.getClassType(Naming.toPathName(imp.getTypeReference())).getMethods();
                    for (int j = 0; j < ml.size(); j++) {
                        Method m = ml.get(j);
                        if (m.isStatic() && m.getName().equals(mr.getName()))
                            result.add(m);
                    }
                }
        }
        List<Type> sig = makeSignature(mr.getArguments());
        return doThreePhaseFilter(result, sig, mr.getName(), MiscKit.getParentTypeDeclaration(mr), mr.getTypeArguments());
    }

    public Constructor getConstructor(ConstructorReference cr) {
        Constructor res = (Constructor) this.reference2element.get(cr);
        if (res != null)
            return res;
        List<? extends Constructor> clist = getConstructors(cr);
        if (clist == null || clist.isEmpty()) {
            getErrorHandler().reportError(new UnresolvedReferenceException(Format.toString("Could not resolve %c \"%s\" @%p in %f (05)", cr), cr));
            return getNameInfo().getUnknownConstructor();
        }
        if (clist.size() > 1)
            getErrorHandler().reportError(new AmbiguousReferenceException(Format.toString("%c \"%s\" @%p in %f is ambiguous - it could be one of ", cr) + Format.toString("%N", clist), cr, clist));
        res = clist.get(0);
        this.reference2element.put(cr, res);
        return res;
    }

    public List<? extends Constructor> getConstructors(ConstructorReference cr) {
        updateModel();
        ClassType type = null;
        if (cr instanceof New) {
            New n = (New) cr;
            ReferencePrefix rp = n.getReferencePrefix();
            if (rp != null) ;
            type = (ClassType) getType(n.getTypeReference());
        } else if (cr instanceof recoder.java.reference.ThisConstructorReference) {
            type = getContainingClassType(cr);
        } else if (cr instanceof recoder.java.reference.SuperConstructorReference) {
            type = getContainingClassType(cr);
            List<? extends ClassType> superTypes = getSupertypes(type);
            for (int i = 0; i < superTypes.size(); i++) {
                type = superTypes.get(i);
                if (!type.isInterface())
                    break;
            }
        } else if (cr instanceof recoder.java.reference.EnumConstructorReference) {
            type = getContainingClassType(cr);
        } else {
            Debug.error("Unknown Constructor Reference " + cr);
        }
        if (type == null) {
            getErrorHandler().reportError(new UnresolvedReferenceException(Format.toString("Could not resolve %c \"%s\" @%p in %f (06)", cr), cr));
            List<Constructor> list = new ArrayList<Constructor>(1);
            list.add(getNameInfo().getUnknownConstructor());
            return list;
        }
        return getConstructors(type, makeSignature(cr.getArguments()));
    }

    public List<TypeDeclaration> getTypes(TypeDeclaration td) {
        Debug.assertNonnull(td);
        updateModel();
        ASTList<MemberDeclaration> aSTList = td.getMembers();
        if (aSTList == null)
            return new ArrayList<TypeDeclaration>(0);
        int s = aSTList.size();
        List<TypeDeclaration> result = new ArrayList<TypeDeclaration>();
        for (int i = 0; i < s; i++) {
            MemberDeclaration m = aSTList.get(i);
            if (m instanceof TypeDeclaration)
                result.add((TypeDeclaration) m);
        }
        return result;
    }

    public List<FieldSpecification> getFields(TypeDeclaration td) {
        Debug.assertNonnull(td);
        updateModel();
        ASTList<MemberDeclaration> aSTList = td.getMembers();
        if (aSTList == null)
            return new ArrayList<FieldSpecification>(0);
        int s = aSTList.size();
        List<FieldSpecification> result = new ArrayList<FieldSpecification>();
        for (int i = 0; i < s; i++) {
            MemberDeclaration m = aSTList.get(i);
            if (m instanceof FieldDeclaration) {
                result.addAll(((FieldDeclaration) m).getFieldSpecifications());
            } else if (m instanceof EnumConstantDeclaration) {
                result.add(((EnumConstantDeclaration) m).getEnumConstantSpecification());
            }
        }
        return result;
    }

    public List<Method> getMethods(TypeDeclaration td) {
        Debug.assertNonnull(td);
        updateModel();
        ASTList<MemberDeclaration> aSTList = td.getMembers();
        if (aSTList == null && !(td instanceof EnumDeclaration))
            return new ArrayList<Method>(0);
        int s = (aSTList == null) ? 0 : aSTList.size();
        List<Method> result = new ArrayList<Method>();
        for (int i = 0; i < s; i++) {
            MemberDeclaration m = aSTList.get(i);
            if (m instanceof MethodDeclaration &&
                    !(m instanceof ConstructorDeclaration))
                result.add(m);
        }
        if (td instanceof EnumDeclaration) {
            List<ImplicitEnumMethod> rl = this.serviceConfiguration.getImplicitElementInfo().getImplicitEnumMethods((EnumDeclaration) td);
            result.add(rl.get(0));
            result.add(rl.get(1));
        }
        return result;
    }

    public List<Constructor> getConstructors(TypeDeclaration td) {
        Debug.assertNonnull(td);
        updateModel();
        List<Constructor> result = new ArrayList<Constructor>(2);
        ASTList<MemberDeclaration> aSTList = td.getMembers();
        int s = (aSTList == null) ? 0 : aSTList.size();
        for (int i = 0; i < s; i++) {
            MemberDeclaration m = aSTList.get(i);
            if (m instanceof ConstructorDeclaration)
                result.add(m);
        }
        if (result.isEmpty() && !td.isInterface() && td.getName() != null)
            result.add(this.serviceConfiguration.getImplicitElementInfo().getDefaultConstructor(td));
        return result;
    }

    public Package getPackage(PackageReference pr) {
        Package res = (Package) this.reference2element.get(pr);
        if (res != null)
            return res;
        res = getNameInfo().createPackage(Naming.toPathName(pr));
        if (res != null)
            this.reference2element.put(pr, res);
        return res;
    }

    public Package getPackage(ProgramModelElement pme) {
        Debug.assertNonnull(pme);
        updateModel();
        Package result = null;
        ProgramElement pe = getDeclaration(pme);
        if (pe == null) {
            result = pme.getProgramModelInfo().getPackage(pme);
        } else {
            result = getNameInfo().createPackage(Naming.getPackageName(UnitKit.getCompilationUnit(pe)));
        }
        return result;
    }

    public List<? extends ClassType> getTypes(ClassTypeContainer ctc) {
        NonTerminalProgramElement nonTerminalProgramElement;
        Debug.assertNonnull(ctc);
        updateModel();
        ProgramElement decl = getDeclaration(ctc);
        if (decl == null)
            return ctc.getProgramModelInfo().getTypes(ctc);
        while (decl != null && !(decl instanceof TypeScope))
            nonTerminalProgramElement = decl.getASTParent();
        Debug.assertNonnull(nonTerminalProgramElement, "Internal error - scope inconsistency");
        return ((TypeScope) nonTerminalProgramElement).getTypesInScope();
    }

    public ClassTypeContainer getClassTypeContainer(ClassType ct) {
        NonTerminalProgramElement nonTerminalProgramElement1;
        Debug.assertNonnull(ct);
        TypeDeclaration td = getTypeDeclaration(ct);
        if (td == null)
            return ct.getProgramModelInfo().getClassTypeContainer(ct);
        TypeDeclaration typeDeclaration1 = td;
        NonTerminalProgramElement par = typeDeclaration1.getASTParent();
        while (par != null) {
            nonTerminalProgramElement1 = par;
            if (nonTerminalProgramElement1 instanceof ClassTypeContainer)
                return (ClassTypeContainer) nonTerminalProgramElement1;
            par = nonTerminalProgramElement1.getASTParent();
        }
        return getNameInfo().createPackage(Naming.getPackageName((CompilationUnit) nonTerminalProgramElement1));
    }

    List<ClassType> getTypeList(List<TypeReference> trl) {
        updateModel();
        int s = (trl != null) ? trl.size() : 0;
        List<ClassType> result = new ArrayList<ClassType>(s);
        for (int i = 0; i < s; i++)
            result.add((ClassType) getType(trl.get(i)));
        return result;
    }

    void addToTypeList(ArrayList<ClassType> result, List<TypeReference> trl) {
        int s = (trl != null) ? trl.size() : 0;
        result.ensureCapacity(result.size() + s);
        for (int i = 0; i < s; i++) {
            TypeReference tr = trl.get(i);
            if (tr != null) {
                ClassType ct = (ClassType) getType(tr);
                if (ct == null) {
                    getErrorHandler().reportError(new UnresolvedReferenceException(Format.toString("Unable to resolve %c \"%s\" @%p in %f", tr), tr));
                    ct = getNameInfo().getUnknownClassType();
                }
                result.add(ct);
            }
        }
    }

    public List<ClassType> getSupertypes(ClassType ct) {
        Debug.assertNonnull(ct);
        updateModel();
        TypeDeclaration td = getTypeDeclaration(ct);
        if (td == null)
            return ct.getProgramModelInfo().getSupertypes(ct);
        DefaultProgramModelInfo.ClassTypeCacheEntry ctce = this.classTypeCache.get(ct);
        if (ctce == null)
            this.classTypeCache.put(ct, ctce = new DefaultProgramModelInfo.ClassTypeCacheEntry());
        if (ctce.supertypes != null)
            return ctce.supertypes;
        ArrayList<ClassType> res = new ArrayList<ClassType>();
        if (td instanceof EnumDeclaration) {
            res.add(getNameInfo().getJavaLangEnum());
            res.add(getNameInfo().getJavaLangObject());
        } else if (td instanceof recoder.java.declaration.AnnotationDeclaration) {
            res.add(getNameInfo().getJavaLangAnnotationAnnotation());
            res.add(getNameInfo().getJavaLangObject());
        } else if (td instanceof InterfaceDeclaration) {
            InterfaceDeclaration id = (InterfaceDeclaration) td;
            Extends ext = id.getExtendedTypes();
            if (ext != null)
                addToTypeList(res, ext.getSupertypes());
            res.add(getNameInfo().getJavaLangObject());
        } else if (td instanceof TypeParameterDeclaration) {
            TypeParameterDeclaration tp = (TypeParameterDeclaration) td;
            if (tp.getBounds() == null || tp.getBounds().size() == 0) {
                res.add(getNameInfo().getJavaLangObject());
            } else {
                for (TypeReference tr : tp.getBounds()) {
                    String name = tr.getName();
                    if (tr.getReferencePrefix() != null)
                        name = Naming.toPathName(tr.getReferencePrefix(), name);
                    res.add((ClassType) getType(name, tp.getASTParent()));
                }
            }
        } else {
            ClassDeclaration cd = (ClassDeclaration) td;
            TypeDeclarationContainer con = cd.getParent();
            if (con instanceof New) {
                TypeReference tr = ((New) con).getTypeReference();
                res.add((ClassType) getType(tr));
            } else {
                Extends ext = cd.getExtendedTypes();
                if (ext != null)
                    addToTypeList(res, ext.getSupertypes());
                Implements imp = cd.getImplementedTypes();
                if (imp != null)
                    addToTypeList(res, imp.getSupertypes());
            }
            if (res.isEmpty()) {
                ClassType jlo = getNameInfo().getJavaLangObject();
                if (ct != jlo)
                    res.add(jlo);
            }
        }
        return ctce.supertypes = res;
    }

    public List<? extends Field> getFields(ClassType ct) {
        Debug.assertNonnull(ct);
        updateModel();
        List<? extends Field> result = null;
        TypeDeclaration td = getTypeDeclaration(ct);
        if (td == null) {
            result = ct.getProgramModelInfo().getFields(ct);
        } else {
            result = getFields(td);
        }
        return result;
    }

    public List<Method> getMethods(ClassType ct) {
        Debug.assertNonnull(ct);
        updateModel();
        List<Method> result = null;
        TypeDeclaration td = getTypeDeclaration(ct);
        if (td == null) {
            result = ct.getProgramModelInfo().getMethods(ct);
        } else {
            result = getMethods(td);
        }
        return result;
    }

    public List<? extends Constructor> getConstructors(ClassType ct) {
        Debug.assertNonnull(ct);
        updateModel();
        List<? extends Constructor> result = null;
        TypeDeclaration td = getTypeDeclaration(ct);
        if (td == null) {
            result = ct.getProgramModelInfo().getConstructors(ct);
        } else {
            result = getConstructors(td);
        }
        return result;
    }

    public List<Type> getSignature(Method m) {
        Debug.assertNonnull(m);
        updateModel();
        List<Type> result = new ArrayList<Type>(0);
        MethodDeclaration md = getMethodDeclaration(m);
        if (md == null) {
            result = m.getProgramModelInfo().getSignature(m);
        } else {
            ASTList<ParameterDeclaration> aSTList = md.getParameters();
            int params = (aSTList == null) ? 0 : aSTList.size();
            if (params > 0) {
                ArrayList<Type> res = new ArrayList<Type>(params);
                result = res;
                for (int i = 0; i < params; i++) {
                    Type ptype = getType(aSTList.get(i).getVariables().get(0));
                    res.add(ptype);
                }
            }
        }
        return result;
    }

    public List<ClassType> getExceptions(Method m) {
        Debug.assertNonnull(m);
        updateModel();
        List<ClassType> result = new ArrayList<ClassType>(0);
        MethodDeclaration md = getMethodDeclaration(m);
        if (md == null) {
            result = m.getProgramModelInfo().getExceptions(m);
        } else {
            Throws t = md.getThrown();
            if (t != null)
                result = getTypeList(t.getExceptions());
        }
        return result;
    }

    public Type getReturnType(Method m) {
        Debug.assertNonnull(m);
        updateModel();
        Type result = null;
        MethodDeclaration md = getMethodDeclaration(m);
        if (md == null) {
            result = m.getProgramModelInfo().getReturnType(m);
        } else {
            TypeReference tr = md.getTypeReference();
            if (tr != null && !"void".equals(tr.getName()))
                result = getType(tr);
        }
        return result;
    }

    public Type getAnnotationType(AnnotationUseSpecification au) {
        Debug.assertNonnull(au);
        updateModel();
        Type result = null;
        TypeReference tr = au.getTypeReference();
        if (tr != null)
            result = getType(tr);
        return result;
    }

    public Reference resolveURQ(UncollatedReferenceQualifier urq) {
        NonTerminalProgramElement parent = urq.getASTParent();
        return resolveURQ(urq, (!(parent instanceof TypeReference) && !(parent instanceof PackageReference)));
    }

    protected Reference resolveURQ(UncollatedReferenceQualifier urq, boolean allowVariables) {
        UncollatedReferenceQualifier uncollatedReferenceQualifier;
        FieldReference fieldReference;
        Debug.assertNonnull(urq);
        ReferencePrefix rp = urq.getReferencePrefix();
        if (rp instanceof UncollatedReferenceQualifier)
            rp = (ReferencePrefix) resolveURQ((UncollatedReferenceQualifier) rp, allowVariables);
        updateModel();
        Reference result = null;
        NameInfo ni = getNameInfo();
        NonTerminalProgramElement parent = urq.getASTParent();
        String urqName = urq.getName();
        if (rp == null) {
            VariableReference variableReference;
            if (allowVariables) {
                Variable v = getVariable(urqName, urq);
                if (v != null) {
                    variableReference = (v instanceof Field) ? urq.toFieldReference() : urq.toVariableReference();
                    this.reference2element.put(variableReference, v);
                }
            }
            if (variableReference == null) {
                Package pkg = ni.getPackage(urqName);
                if (pkg != null) {
                    PackageReference packageReference = urq.toPackageReference();
                    this.reference2element.put(packageReference, pkg);
                } else {
                    Type t = getType(urqName, urq);
                    if (t != null) {
                        TypeReference typeReference = urq.toTypeReference();
                        this.reference2element.put(typeReference, t);
                    } else if (urqName.charAt(0) >= 'A' && urqName.charAt(0) <= 'Z') {
                        TypeReference typeReference = urq.toTypeReference();
                        getErrorHandler().reportError(new UnresolvedReferenceException(Format.toString("Could not resolve %c \"%s\" @%p in %f (07b)", urq), urq));
                    } else {
                        try {
                            PackageReference packageReference = urq.toPackageReference();
                        } catch (ClassCastException cce) {
                            getErrorHandler().reportError(new UnresolvedReferenceException(Format.toString("Could not resolve %c \"%s\" @%p in %f (07)", urq), urq));
                            TypeReference typeReference = urq.toTypeReference();
                        }
                    }
                }
            }
        } else if (rp instanceof ThisReference) {
            TypeDeclaration typeDeclaration;
            ReferencePrefix rpp = ((ThisReference) rp).getReferencePrefix();
            if (rpp == null) {
                TypeScope thisScope = (TypeScope) getContainingClassType(urq);
            } else {
                TypeReference tr = (rpp instanceof TypeReference) ? (TypeReference) rpp : (TypeReference) resolveURQ((UncollatedReferenceQualifier) rpp, false);
                typeDeclaration = (TypeDeclaration) getType(tr);
            }
            Variable v = getVariable(urqName, typeDeclaration);
            if (v != null) {
                VariableReference variableReference = urq.toFieldReference();
                this.reference2element.put(variableReference, v);
            } else {
                ClassType classType = typeDeclaration.getTypeInScope(urqName);
                if (classType != null) {
                    TypeReference typeReference = urq.toTypeReference();
                    this.reference2element.put(typeReference, classType);
                }
            }
        } else if (rp instanceof SuperReference) {
            ClassType superType = (ClassType) getType(rp);
            Field f = getInheritedField(urq.getName(), superType);
            if (f != null) {
                VariableReference variableReference = urq.toFieldReference();
                this.reference2element.put(variableReference, f);
            } else {
                String fullname = Naming.getFullName(superType, urq.getName());
                ClassType ct = ni.getClassType(fullname);
                if (ct != null) {
                    TypeReference typeReference = urq.toTypeReference();
                    this.reference2element.put(typeReference, ct);
                }
            }
        } else if (rp instanceof PackageReference) {
            String fullRefName = Naming.toPathName(urq);
            Package pkg = ni.getPackage(fullRefName);
            if (pkg != null) {
                PackageReference packageReference = urq.toPackageReference();
                this.reference2element.put(packageReference, pkg);
            } else {
                ClassType classType = ni.getClassType(fullRefName);
                if (classType != null) {
                    TypeReference typeReference = urq.toTypeReference();
                    this.reference2element.put(typeReference, classType);
                } else if (urq.getReferenceSuffix() instanceof MethodReference || (allowVariables && urq.getReferenceSuffix() instanceof FieldReference)) {
                    TypeReference typeReference = urq.toTypeReference();
                } else {
                    PackageReference packageReference = urq.toPackageReference();
                }
            }
        } else if (rp instanceof TypeReference || rp instanceof Expression) {
            Type refT = getType(rp);
            if (refT instanceof ClassType) {
                VariableReference variableReference;
                ClassType ct = (ClassType) refT;
                if (allowVariables) {
                    Field f = getInheritedField(urq.getName(), ct);
                    if (f != null) {
                        variableReference = urq.toFieldReference();
                        this.reference2element.put(variableReference, f);
                    }
                }
                if (variableReference == null) {
                    String fullname = Naming.getFullName((ClassTypeContainer) refT, urq.getName());
                    ClassType innerType = ni.getClassType(fullname);
                    if (innerType != null) {
                        TypeReference typeReference = urq.toTypeReference();
                        this.reference2element.put(typeReference, innerType);
                    }
                }
            } else if (refT instanceof ArrayType) {
                if (allowVariables && urq.getName() == "length") {
                    ArrayLengthReference arrayLengthReference = urq.toArrayLengthReference();
                } else {
                    getErrorHandler().reportError(new UnresolvedReferenceException(Format.toString("Could not resolve %c \"%s\" @%p in %f (08)", urq), urq));
                    uncollatedReferenceQualifier = urq;
                }
            } else {
                getErrorHandler().reportError(new UnresolvedReferenceException(Format.toString("Could not resolve %c \"%s\" @%p in %f (09)", rp), rp));
                uncollatedReferenceQualifier = urq;
            }
        } else {
            getErrorHandler().reportError(new UnresolvedReferenceException(Format.toString("Could not resolve %c \"%s\" @%p in %f (10)", rp), rp));
            uncollatedReferenceQualifier = urq;
        }
        if (uncollatedReferenceQualifier == null) {
            getErrorHandler().reportError(new UnresolvedReferenceException(Format.toString("Could not resolve %c \"%s\" @%p in %f (11)", urq), urq));
            uncollatedReferenceQualifier = urq;
        } else if (uncollatedReferenceQualifier != urq) {
            try {
                parent.replaceChild(urq, uncollatedReferenceQualifier);
            } catch (ClassCastException cce) {
                boolean throwAgain = true;
                if (!(uncollatedReferenceQualifier instanceof Expression) &&
                        uncollatedReferenceQualifier instanceof PackageReference) {
                    PackageReference pr = (PackageReference) uncollatedReferenceQualifier;
                    ProgramFactory pf = uncollatedReferenceQualifier.getFactory();
                    Package pack = pf.getServiceConfiguration().getNameInfo().getPackage(pr.toSource());
                    if (pack == null) {
                        PackageReference pkgToBeReplacedByType = pr.getPackageReference();
                        PackageReference newPr = null;
                        TypeReference typeRef = null;
                        if (pkgToBeReplacedByType != null) {
                            newPr = pr.getPackageReference().getPackageReference();
                            typeRef = pf.createTypeReference(newPr, pkgToBeReplacedByType.getIdentifier());
                        }
                        fieldReference = pf.createFieldReference(typeRef, pr.getIdentifier());
                        fieldReference.setStartPosition(pr.getStartPosition());
                        fieldReference.setEndPosition(pr.getEndPosition());
                        fieldReference.setRelativePosition(pr.getRelativePosition());
                        fieldReference.setComments(pr.getComments());
                        throwAgain = false;
                        parent.replaceChild(urq, fieldReference);
                    }
                }
                if (throwAgain)
                    throw cce;
            }
            Debug.assertBoolean((parent == fieldReference.getASTParent()));
        }
        return fieldReference;
    }

    private boolean java5Allowed() {
        return this.serviceConfiguration.getProjectSettings().java5Allowed();
    }

    public List<Statement> getSucceedingStatements(Statement s) {
        List<Statement> list = new ArrayList<Statement>();
        if (s instanceof LoopStatement) {
            LoopStatement loop = (LoopStatement) s;
            switch (getBooleanStatus(loop.getGuard())) {
                case 1:
                    if (loop.getBody() != null)
                        list.add(loop.getBody());
                    break;
                case 0:
                    if (loop.isCheckedBeforeIteration()) {
                        addSequentialFollower(s, list);
                        break;
                    }
                    if (loop.getBody() != null)
                        list.add(loop.getBody());
                    addSequentialFollower(s, list);
                    break;
                case -1:
                    if (loop.getBody() != null)
                        list.add(loop.getBody());
                    addSequentialFollower(s, list);
                    break;
            }
        } else if (s instanceof LabeledStatement) {
            list.add(((LabeledStatement) s).getBody());
        } else if (s instanceof StatementBlock) {
            ASTList<Statement> aSTList = ((StatementBlock) s).getBody();
            if (aSTList == null || aSTList.isEmpty()) {
                addSequentialFollower(s, list);
            } else {
                list.add(aSTList.get(0));
            }
        } else if (s instanceof SynchronizedBlock) {
            ASTList<Statement> aSTList = ((SynchronizedBlock) s).getBody().getBody();
            if (aSTList == null || aSTList.isEmpty()) {
                addSequentialFollower(s, list);
            } else {
                list.add(aSTList.get(0));
            }
        } else if (s instanceof If) {
            If ifstmt = (If) s;
            if (ifstmt.getElse() != null) {
                list.add(ifstmt.getThen().getBody());
                list.add(ifstmt.getElse().getBody());
            } else {
                list.add(ifstmt.getThen().getBody());
                addSequentialFollower(s, list);
            }
        } else if (s instanceof Switch) {
            ASTList<Branch> aSTList = ((Switch) s).getBranchList();
            if (aSTList == null || aSTList.isEmpty()) {
                addSequentialFollower(s, list);
            } else {
                boolean hasDefault = false;
                for (int i = 0, c = aSTList.size(); i < c; i++) {
                    ASTList<Statement> aSTList1;
                    Branch b = aSTList.get(i);
                    List<Statement> stats = null;
                    if (b instanceof Default) {
                        aSTList1 = ((Default) b).getBody();
                        if (i < c - 1 || (aSTList1 != null && !aSTList1.isEmpty()))
                            hasDefault = true;
                    } else if (b instanceof Case) {
                        aSTList1 = ((Case) b).getBody();
                    }
                    if (aSTList1 != null && !aSTList1.isEmpty())
                        list.add(aSTList1.get(0));
                }
                if (!hasDefault)
                    addSequentialFollower(s, list);
            }
        } else if (s instanceof Try) {
            list.add(((Try) s).getBody());
            ASTList<Branch> aSTList = ((Try) s).getBranchList();
            if (aSTList == null || aSTList.isEmpty()) {
                addSequentialFollower(s, list);
                return list;
            }
            for (int i = 0; i < aSTList.size(); i++) {
                Branch b = aSTList.get(i);
                if (b instanceof Catch) {
                    Catch ca = (Catch) b;
                    boolean newException = true;
                    if (i > 0) {
                        ClassType ex = (ClassType) getType(ca.getParameterDeclaration().getTypeReference());
                        for (int j = i - 1; j >= 0; j--) {
                            if (aSTList.get(j) instanceof Catch) {
                                ClassType dx = (ClassType) getType(((Catch) aSTList.get(j)).getParameterDeclaration().getTypeReference());
                                if (isSubtype(ex, dx)) {
                                    newException = false;
                                    break;
                                }
                            }
                        }
                    }
                    if (newException)
                        list.add(ca.getBody());
                } else if (b instanceof Finally) {
                    list.add(((Finally) b).getBody());
                }
            }
            addSequentialFollower(s, list);
        } else if (s instanceof recoder.java.statement.ExpressionJumpStatement) {
            list.add(METHOD_EXIT);
        } else if (s instanceof Break) {
            if (((Break) s).getIdentifier() == null) {
                addSequentialFollower(findInnermostBreakBlock(s), list);
            } else {
                addSequentialFollower(StatementKit.getCorrespondingLabel((LabelJumpStatement) s), list);
            }
        } else if (s instanceof Continue) {
            if (((Continue) s).getIdentifier() == null) {
                list.add(findInnermostLoop(s));
            } else {
                list.add(StatementKit.getCorrespondingLabel((LabelJumpStatement) s).getBody());
            }
        } else {
            addSequentialFollower(s, list);
        }
        return list;
    }

    private int getBooleanStatus(Expression expr) {
        if (expr == null)
            return 1;
        ConstantEvaluator.EvaluationResult evr = new ConstantEvaluator.EvaluationResult();
        if (this.serviceConfiguration.getConstantEvaluator().isCompileTimeConstant(expr, evr))
            return evr.getBoolean() ? 1 : 0;
        return -1;
    }

    public void register(ProgramElement pe) {
        Debug.assertNonnull(pe);
        if (pe instanceof CompilationUnit) {
            if (!((CompilationUnit) pe).isDefinedScope())
                analyzeProgramElement(pe);
        } else {
            Debug.assertNonnull(pe.getASTParent());
            analyzeProgramElement(pe);
        }
    }

    private void analyzeProgramElement(ProgramElement pe) {
        Debug.assertNonnull(pe);
        if (pe instanceof CompilationUnit) {
            CompilationUnit cu = (CompilationUnit) pe;
            String packageName = Naming.getPackageName(cu);
            getNameInfo().createPackage(packageName);
        }
        analyzeProgramElement0(pe);
    }

    private void analyzeProgramElement0(ProgramElement pe) {
        if (pe instanceof recoder.java.TerminalProgramElement)
            return;
        if (pe instanceof ScopeDefiningElement) {
            ((ScopeDefiningElement) pe).setDefinedScope(true);
            if (pe instanceof MethodDeclaration) {
                ((MethodDeclaration) pe).setProgramModelInfo(this);
            } else if (pe instanceof TypeDeclaration) {
                TypeDeclaration td = (TypeDeclaration) pe;
                td.setProgramModelInfo(this);
                String typename = td.getName();
                if (typename != null) {
                    NonTerminalProgramElement parent = pe.getASTParent();
                    while (!(parent instanceof TypeScope))
                        parent = parent.getASTParent();
                    TypeScope scope = (TypeScope) parent;
                    ClassType dup = scope.getTypeInScope(typename);
                    if (dup != null && dup != td)
                        getErrorHandler().reportError(new AmbiguousDeclarationException("Duplicate declaration of " + Format.toString("%c \"%N\" @%p in %f", td) + " - was " + Format.toString("%c \"%N\" @%p in %f", dup), td, dup));
                    scope.addTypeToScope(td, typename);
                    getNameInfo().register(td);
                }
            }
        } else if (pe instanceof VariableSpecification) {
            VariableSpecification vs = (VariableSpecification) pe;
            vs.setProgramModelInfo(this);
            NonTerminalProgramElement parent = vs.getASTParent().getASTParent();
            while (!(parent instanceof VariableScope))
                parent = parent.getASTParent();
            VariableScope scope = (VariableScope) parent;
            String vname = vs.getName();
            VariableSpecification variableSpecification1 = scope.getVariableInScope(vname);
            if (variableSpecification1 != null && variableSpecification1 != vs)
                getErrorHandler().reportError(new AmbiguousDeclarationException("Duplicate declaration of " + Format.toString("%c \"%N\" @%p in %f", vs) + " - was " + Format.toString("%c \"%N\" @%p in %f", variableSpecification1), vs, variableSpecification1));
            if (!(scope instanceof TypeDeclaration))
                for (VariableScope outer = findOuterVariableScope(scope); !(outer instanceof TypeDeclaration); outer = findOuterVariableScope(outer)) {
                    variableSpecification1 = outer.getVariableInScope(vname);
                    if (variableSpecification1 != null)
                        getErrorHandler().reportError(new AmbiguousDeclarationException("Hidden local declaration: " + Format.toString("%c \"%N\" @%p in %f", vs) + " - hides " + Format.toString("%c \"%N\" @%p in %f", variableSpecification1), vs, variableSpecification1));
                }
            scope.addVariableToScope(vs);
            if (vs instanceof FieldSpecification)
                getNameInfo().register((Field) vs);
        }
        NonTerminalProgramElement cont = (NonTerminalProgramElement) pe;
        int childCount = cont.getChildCount();
        for (int i = 0; i < childCount; i++)
            analyzeProgramElement0(cont.getChildAt(i));
    }

    void unregister(TypeDeclaration td) {
        unregister(td, td.getName());
    }

    void unregister(TypeDeclaration td, String shortname) {
        if (shortname != null)
            ((TypeScope) td.getASTParent()).removeTypeFromScope(shortname);
        getNameInfo().unregisterClassType(td.getFullName());
        DefaultProgramModelInfo.ClassTypeCacheEntry ctce = this.classTypeCache.get(td);
        if (ctce != null) {
            List<? extends ClassType> superTypes = ctce.supertypes;
            if (superTypes != null)
                for (int i = superTypes.size() - 1; i >= 0; i--)
                    removeSubtype(td, superTypes.get(i));
        }
    }

    void unregister(VariableSpecification vs) {
        unregister(vs, vs.getName());
    }

    void unregister(VariableSpecification vs, String shortname) {
        NonTerminalProgramElement nonTerminalProgramElement = vs.getASTParent().getASTParent();
        while (!(nonTerminalProgramElement instanceof VariableScope))
            nonTerminalProgramElement = nonTerminalProgramElement.getASTParent();
        ((VariableScope) nonTerminalProgramElement).removeVariableFromScope(shortname);
        if (vs instanceof FieldSpecification) {
            ClassType ct = ((Field) vs).getContainingClassType();
            getNameInfo().unregisterField(Naming.getFullName(ct, shortname));
        }
    }

    void unregister(ProgramElement pe) {
        Debug.assertNonnull(pe);
        if (pe instanceof TypeDeclaration) {
            unregister((TypeDeclaration) pe);
        } else if (pe instanceof VariableSpecification) {
            unregister((VariableSpecification) pe);
        } else if (pe instanceof VariableDeclaration) {
            List<? extends VariableSpecification> vspecs = ((VariableDeclaration) pe).getVariables();
            for (int i = vspecs.size() - 1; i >= 0; i--)
                unregister(vspecs.get(i));
        }
        TreeWalker tw = new TreeWalker(pe);
        while (tw.next()) {
            pe = tw.getProgramElement();
            if (pe instanceof ScopeDefiningElement)
                flushScopes((ScopeDefiningElement) pe);
        }
    }

    void flushScopes(ScopeDefiningElement sde) {
        DefaultNameInfo dni = (DefaultNameInfo) getNameInfo();
        if (sde instanceof TypeScope) {
            List<? extends ClassType> ctl = ((TypeScope) sde).getTypesInScope();
            if (sde instanceof CompilationUnit) {
                for (int j = ctl.size() - 1; j >= 0; j--) {
                    ClassType ct = ctl.get(j);
                    if (ct instanceof TypeDeclaration && ((TypeDeclaration) ct).getASTParent() == sde)
                        dni.unregisterClassType(ct.getFullName());
                }
            } else {
                for (int j = ctl.size() - 1; j >= 0; j--)
                    dni.unregisterClassType(ctl.get(j).getFullName());
            }
        }
        if (sde instanceof TypeDeclaration) {
            List<FieldSpecification> fl = ((TypeDeclaration) sde).getFieldsInScope();
            for (int j = fl.size() - 1; j >= 0; j--)
                dni.unregisterField(fl.get(j).getFullName());
        }
        sde.setDefinedScope(false);
    }

    public void reset() {
        super.reset();
        this.reference2element.clear();
        SourceFileRepository sfr = this.serviceConfiguration.getSourceFileRepository();
        List<CompilationUnit> cul = sfr.getCompilationUnits();
        DefaultNameInfo dni = (DefaultNameInfo) getNameInfo();
        dni.unregisterPackages();
        for (int i = cul.size() - 1; i >= 0; i--) {
            CompilationUnit cu = cul.get(i);
            unregister(cu);
            analyzeProgramElement(cu);
        }
    }
}
