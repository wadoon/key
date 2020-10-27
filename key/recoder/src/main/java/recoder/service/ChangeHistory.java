package recoder.service;

import recoder.AbstractService;
import recoder.ServiceConfiguration;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.expression.ArrayInitializer;
import recoder.java.expression.Operator;
import recoder.java.expression.operator.New;
import recoder.java.expression.operator.NewArray;
import recoder.java.expression.operator.TypeOperator;
import recoder.java.reference.*;
import recoder.java.statement.*;
import recoder.kit.Transformation;
import recoder.kit.UnitKit;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.util.Debug;

import java.util.*;

public class ChangeHistory extends AbstractService {
    private static final boolean DEBUG = false;
    private final Map<ProgramElement, TreeChange> root2change;
    private final EventObject updateEvent;
    private List<TreeChange> changeList;
    private boolean needsUpdate;
    private boolean isUpdating;
    private boolean delayedUpdate;
    private Object[] reportStack;
    private int reportCount;
    private ChangeHistoryListener[] changeListeners;
    private ModelUpdateListener[] updateListeners;

    public ChangeHistory(ServiceConfiguration config) {
        super(config);
        this.changeList = new ArrayList<TreeChange>();
        this.root2change = new HashMap<ProgramElement, TreeChange>();
        this.needsUpdate = false;
        this.isUpdating = false;
        this.delayedUpdate = false;
        this.reportStack = new Object[8];
        this.reportCount = 0;
        this.changeListeners = new ChangeHistoryListener[0];
        this.updateListeners = new ModelUpdateListener[0];
        this.updateEvent = new EventObject(this);
    }

    public void addChangeHistoryListener(ChangeHistoryListener chl) {
        synchronized (this.changeListeners) {
            ChangeHistoryListener[] newListeners = new ChangeHistoryListener[this.changeListeners.length + 1];
            System.arraycopy(this.changeListeners, 0, newListeners, 0, this.changeListeners.length);
            newListeners[this.changeListeners.length] = chl;
            this.changeListeners = newListeners;
        }
    }

    public void removeChangeHistoryListener(ChangeHistoryListener chl) {
        synchronized (this.changeListeners) {
            for (int i = this.changeListeners.length - 1; i >= 0; i--) {
                if (this.changeListeners[i] == chl) {
                    ChangeHistoryListener[] newListeners = new ChangeHistoryListener[this.changeListeners.length - 1];
                    if (i > 0)
                        System.arraycopy(this.changeListeners, 0, newListeners, 0, i);
                    if (i < this.changeListeners.length - 1)
                        System.arraycopy(this.changeListeners, i + 1, newListeners, i, this.changeListeners.length - 1 - i);
                    this.changeListeners = newListeners;
                    break;
                }
            }
        }
    }

    public void addModelUpdateListener(ModelUpdateListener l) {
        synchronized (this.updateListeners) {
            ModelUpdateListener[] newListeners = new ModelUpdateListener[this.updateListeners.length + 1];
            System.arraycopy(this.updateListeners, 0, newListeners, 0, this.updateListeners.length);
            newListeners[this.updateListeners.length] = l;
            this.updateListeners = newListeners;
        }
    }

    public void removeModelUpdateListener(ModelUpdateListener l) {
        synchronized (this.updateListeners) {
            for (int i = this.updateListeners.length - 1; i >= 0; i--) {
                if (this.updateListeners[i] == l) {
                    ModelUpdateListener[] newListeners = new ModelUpdateListener[this.updateListeners.length - 1];
                    if (i > 0)
                        System.arraycopy(this.updateListeners, 0, newListeners, 0, i);
                    if (i < this.updateListeners.length - 1)
                        System.arraycopy(this.updateListeners, i + 1, newListeners, i, this.updateListeners.length - 1 - i);
                    this.updateListeners = newListeners;
                    break;
                }
            }
        }
    }

    private void checkConflict(TreeChange oldChange, TreeChange newChange) {
        boolean sameParent = (newChange.getChangeRootParent() == oldChange.getChangeRootParent());
        if (oldChange instanceof AttachChange) {
            if (newChange instanceof AttachChange)
                if (sameParent) {
                    this.root2change.put(oldChange.getChangeRoot(), oldChange);
                    this.changeList.remove(this.changeList.size() - 1);
                } else {
                    throw new IllegalChangeReportException("Duplicate attachment of one element in different places: " + newChange + " followed " + oldChange);
                }
            if (!(newChange instanceof DetachChange) || sameParent) ;
        } else if (oldChange instanceof DetachChange) {
            if (!(newChange instanceof AttachChange) || sameParent) ;
            if (!(newChange instanceof DetachChange) || sameParent) ;
        }
    }

    public void attached(ProgramElement root) {
        Debug.assertNonnull(root);
        Debug.assertBoolean((root.getASTParent() != null || root instanceof CompilationUnit));
        AttachChange ac = new AttachChange(root);
        enqueueChange(ac);
        pushChange(ac);
    }

    public void detached(ProgramElement root, NonTerminalProgramElement parent, int pos) {
        Debug.assertNonnull(root);
        Debug.assertBoolean((parent != null || root instanceof CompilationUnit));
        DetachChange dc = new DetachChange(root, parent, pos);
        enqueueChange(dc);
        pushChange(dc);
    }

    public void detached(ProgramElement root, int pos) {
        detached(root, root.getASTParent(), pos);
    }

    public void replaced(ProgramElement root, ProgramElement replacement) {
        Debug.assertNonnull(root, replacement);
        NonTerminalProgramElement parent = replacement.getASTParent();
        Debug.assertBoolean((parent != null || replacement instanceof CompilationUnit));
        AttachChange ac = new AttachChange(replacement);
        DetachChange dc = new DetachChange(root, ac);
        enqueueChange(dc);
        enqueueChange(ac);
        pushChange(dc);
        pushChange(ac);
    }

    private void enqueueChange(TreeChange tc) {
        this.changeList.add(tc);
        TreeChange duplicate = this.root2change.put(tc.getChangeRoot(), tc);
        if (duplicate != null)
            checkConflict(duplicate, tc);
        this.needsUpdate = true;
    }

    private TreeChange getTailChange() {
        int s = this.changeList.size();
        return (s == 0) ? null : this.changeList.get(s - 1);
    }

    private void removeTailChange() {
        int s = this.changeList.size();
        TreeChange tc = this.changeList.get(s - 1);
        this.root2change.remove(tc.getChangeRoot());
        this.changeList.remove(s - 1);
        if (s == 1)
            this.needsUpdate = false;
    }

    private void normalize() {
        for (int i = 0, s = this.changeList.size(); i < s; i++) {
            CompilationUnit compilationUnit;
            TreeChange tc = this.changeList.get(i);
            ProgramElement current = tc.getChangeRoot();
            NonTerminalProgramElement parent = tc.getChangeRootParent();
            while (parent != null) {
                NonTerminalProgramElement nonTerminalProgramElement = parent;
                if (this.root2change.containsKey(nonTerminalProgramElement)) {
                    tc.setMinor(true);
                    compilationUnit = UnitKit.getCompilationUnit(nonTerminalProgramElement);
                    break;
                }
                parent = parent.getASTParent();
            }
            tc.setCompilationUnit(compilationUnit);
        }
    }

    public final boolean needsUpdate() {
        return this.needsUpdate;
    }

    public final void updateModel() {
        if (!this.needsUpdate)
            return;
        if (this.isUpdating) {
            this.delayedUpdate = true;
            return;
        }
        synchronized (this.updateListeners) {
            int s = this.updateListeners.length;
            if (s > 0)
                for (int i = 0; i < s; i++)
                    this.updateListeners[i].modelUpdating(this.updateEvent);
        }
        do {
            this.needsUpdate = false;
            this.isUpdating = true;
            normalize();
            ChangeHistoryEvent event = new ChangeHistoryEvent(this, this.changeList);
            this.changeList = new ArrayList<TreeChange>();
            this.root2change.clear();
            ChangeHistoryListener[] listeners = this.changeListeners;
            for (int i = 0, s = listeners.length; i < s; i++)
                listeners[i].modelChanged(event);
            this.isUpdating = false;
            if (!this.delayedUpdate)
                break;
            this.delayedUpdate = false;
        } while (this.needsUpdate);
        synchronized (this.updateListeners) {
            int s = this.updateListeners.length;
            if (s > 0)
                for (int i = 0; i < s; i++)
                    this.updateListeners[i].modelUpdated(this.updateEvent);
        }
    }

    private void pushChange(TreeChange tc) {
        push(tc);
    }

    private void push(Object transformationOrTreeChange) {
        if (this.reportCount == this.reportStack.length) {
            Object[] newt = new Object[this.reportCount * 2];
            System.arraycopy(this.reportStack, 0, newt, 0, this.reportCount);
            this.reportStack = newt;
        }
        this.reportStack[this.reportCount++] = transformationOrTreeChange;
    }

    public void begin(Transformation transformation) {
        push(transformation);
    }

    private void rollback(int position) {
        while (this.reportCount > position) {
            this.reportCount--;
            if (this.reportStack[this.reportCount] instanceof TreeChange) {
                TreeChange lastChange = (TreeChange) this.reportStack[this.reportCount];
                TreeChange undoChange = undo(lastChange);
                if (lastChange == getTailChange()) {
                    removeTailChange();
                } else {
                    enqueueChange(undoChange);
                }
            }
            this.reportStack[this.reportCount] = null;
        }
    }

    private int locate(Transformation transformation) {
        int position = this.reportCount;
        while (position >= 0) {
            position--;
            if (this.reportStack[position] == transformation)
                break;
        }
        return position;
    }

    public void rollback(Transformation transformation) throws NoSuchTransformationException {
        int position = locate(transformation);
        if (position < 0)
            throw new NoSuchTransformationException(transformation);
        rollback(position);
    }

    public void rollback() {
        rollback(0);
    }

    public boolean isReported(Transformation transformation) {
        return (locate(transformation) >= 0);
    }

    public void commit() {
        while (this.reportCount > 0)
            this.reportStack[--this.reportCount] = null;
    }

    private TreeChange undo(TreeChange tc) {
        ProgramElement child = tc.getChangeRoot();
        NonTerminalProgramElement parent = tc.getChangeRootParent();
        if (tc instanceof AttachChange) {
            TreeChange result;
            if (parent != null) {
                int position = parent.getChildPositionCode(child);
                parent.replaceChild(child, null);
                result = new DetachChange(child, parent, position);
            } else {
                result = new DetachChange(child, null, 0);
            }
            return result;
        }
        if (!(tc instanceof DetachChange))
            return null;
        DetachChange dc = (DetachChange) tc;
        int pos = dc.getChangePositionCode();
        int role = pos & 0xF;
        int index = pos >> 4;
        if (parent == null) {
            CompilationUnit x = (CompilationUnit) child;
            x.setDataLocation(null);
        }
        if (parent instanceof CompilationUnit) {
            ASTList<Import> list;
            ASTArrayList aSTArrayList1;
            ASTList<TypeDeclaration> list2;
            ASTArrayList aSTArrayList2;
            CompilationUnit x = (CompilationUnit) parent;
            switch (role) {
                case 0:
                    x.setPackageSpecification((PackageSpecification) child);
                case 1:
                    list = x.getImports();
                    if (list == null) {
                        aSTArrayList1 = new ASTArrayList();
                        x.setImports(aSTArrayList1);
                    }
                    aSTArrayList1.add(index, child);
                case 2:
                    list2 = x.getDeclarations();
                    if (list2 == null) {
                        aSTArrayList2 = new ASTArrayList();
                        x.setDeclarations(aSTArrayList2);
                    }
                    aSTArrayList2.add(index, child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof Import) {
            Import x = (Import) parent;
            switch (role) {
                case 0:
                    x.setReference((TypeReferenceInfix) child);
                case 1:
                    x.setStaticIdentifier((Identifier) child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof PackageSpecification) {
            ASTList<AnnotationUseSpecification> rpel;
            ASTArrayList aSTArrayList;
            PackageSpecification x = (PackageSpecification) parent;
            switch (role) {
                case 0:
                    x.setPackageReference((PackageReference) child);
                case 1:
                    rpel = x.getAnnotations();
                    if (rpel == null) {
                        aSTArrayList = new ASTArrayList();
                        x.setAnnotations(aSTArrayList);
                    }
                    aSTArrayList.add(index, child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof StatementBlock) {
            ASTArrayList aSTArrayList;
            StatementBlock x = (StatementBlock) parent;
            ASTList<Statement> list = x.getBody();
            if (list == null) {
                aSTArrayList = new ASTArrayList();
                x.setBody(aSTArrayList);
            }
            aSTArrayList.add(index, child);
        }
        if (parent instanceof ClassDeclaration) {
            ASTList<DeclarationSpecifier> list;
            ASTArrayList aSTArrayList1;
            ASTList<MemberDeclaration> list2;
            ASTArrayList aSTArrayList2;
            ASTList<TypeParameterDeclaration> list3;
            ASTArrayList aSTArrayList3;
            ClassDeclaration x = (ClassDeclaration) parent;
            switch (role) {
                case 0:
                    list = x.getDeclarationSpecifiers();
                    if (list == null) {
                        aSTArrayList1 = new ASTArrayList();
                        x.setDeclarationSpecifiers(aSTArrayList1);
                    }
                    aSTArrayList1.add(index, child);
                case 1:
                    x.setIdentifier((Identifier) child);
                case 2:
                    x.setExtendedTypes((Extends) child);
                case 3:
                    x.setImplementedTypes((Implements) child);
                case 4:
                    list2 = x.getMembers();
                    if (list2 == null) {
                        aSTArrayList2 = new ASTArrayList();
                        x.setMembers(aSTArrayList2);
                    }
                    aSTArrayList2.add(index, child);
                case 5:
                    list3 = x.getTypeParameters();
                    if (list3 == null) {
                        aSTArrayList3 = new ASTArrayList();
                        x.setTypeParameters(aSTArrayList3);
                    }
                    aSTArrayList3.add(index, child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof EnumDeclaration) {
            ASTList<DeclarationSpecifier> list;
            ASTArrayList aSTArrayList1;
            ASTList<MemberDeclaration> list2;
            ASTArrayList aSTArrayList2;
            EnumDeclaration x = (EnumDeclaration) parent;
            switch (role) {
                case 0:
                    list = x.getDeclarationSpecifiers();
                    if (list == null) {
                        aSTArrayList1 = new ASTArrayList();
                        x.setDeclarationSpecifiers(aSTArrayList1);
                    }
                    aSTArrayList1.add(index, child);
                case 1:
                    x.setIdentifier((Identifier) child);
                case 2:
                    x.setImplementedTypes((Implements) child);
                case 3:
                    list2 = x.getMembers();
                    if (list2 == null) {
                        aSTArrayList2 = new ASTArrayList();
                        x.setMembers(aSTArrayList2);
                    }
                    aSTArrayList2.add(index, child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof ClassInitializer) {
            ASTList<DeclarationSpecifier> list;
            ASTArrayList aSTArrayList;
            ClassInitializer x = (ClassInitializer) parent;
            switch (role) {
                case 0:
                    list = x.getDeclarationSpecifiers();
                    if (list == null) {
                        aSTArrayList = new ASTArrayList();
                        x.setDeclarationSpecifiers(aSTArrayList);
                    }
                    aSTArrayList.add(index, child);
                case 1:
                    x.setBody((StatementBlock) child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof FieldDeclaration) {
            ASTList<DeclarationSpecifier> list;
            ASTArrayList aSTArrayList1;
            ASTList<FieldSpecification> list2;
            ASTArrayList aSTArrayList2;
            FieldDeclaration x = (FieldDeclaration) parent;
            switch (role) {
                case 0:
                    list = x.getDeclarationSpecifiers();
                    if (list == null) {
                        aSTArrayList1 = new ASTArrayList();
                        x.setDeclarationSpecifiers(aSTArrayList1);
                    }
                    aSTArrayList1.add(index, child);
                case 1:
                    x.setTypeReference((TypeReference) child);
                case 2:
                    list2 = x.getFieldSpecifications();
                    if (list2 == null) {
                        aSTArrayList2 = new ASTArrayList();
                        x.setFieldSpecifications(aSTArrayList2);
                    }
                    aSTArrayList2.add(index, child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof InheritanceSpecification) {
            ASTArrayList aSTArrayList;
            InheritanceSpecification x = (InheritanceSpecification) parent;
            ASTList<TypeReference> list = x.getSupertypes();
            if (list == null) {
                aSTArrayList = new ASTArrayList();
                x.setSupertypes(aSTArrayList);
            }
            aSTArrayList.add(index, child);
        }
        if (parent instanceof InterfaceDeclaration) {
            ASTList<DeclarationSpecifier> list;
            ASTArrayList aSTArrayList1;
            ASTList<MemberDeclaration> list2;
            ASTArrayList aSTArrayList2;
            ASTList<TypeParameterDeclaration> list3;
            ASTArrayList aSTArrayList3;
            InterfaceDeclaration x = (InterfaceDeclaration) parent;
            switch (role) {
                case 0:
                    list = x.getDeclarationSpecifiers();
                    if (list == null) {
                        aSTArrayList1 = new ASTArrayList();
                        x.setDeclarationSpecifiers(aSTArrayList1);
                    }
                    aSTArrayList1.add(index, child);
                case 1:
                    x.setIdentifier((Identifier) child);
                case 2:
                    x.setExtendedTypes((Extends) child);
                case 4:
                    list2 = x.getMembers();
                    if (list2 == null) {
                        aSTArrayList2 = new ASTArrayList();
                        x.setMembers(aSTArrayList2);
                    }
                    aSTArrayList2.add(index, child);
                case 5:
                    list3 = x.getTypeParameters();
                    if (list3 == null) {
                        aSTArrayList3 = new ASTArrayList();
                        x.setTypeParameters(aSTArrayList3);
                    }
                    aSTArrayList3.add(index, child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof LocalVariableDeclaration) {
            ASTList<DeclarationSpecifier> list2;
            ASTArrayList aSTArrayList1;
            ASTList<VariableSpecification> list3;
            ASTArrayList aSTArrayList2;
            LocalVariableDeclaration x = (LocalVariableDeclaration) parent;
            switch (role) {
                case 0:
                    list2 = x.getDeclarationSpecifiers();
                    if (list2 == null) {
                        aSTArrayList1 = new ASTArrayList();
                        x.setDeclarationSpecifiers(aSTArrayList1);
                    }
                    aSTArrayList1.add(index, child);
                case 1:
                    x.setTypeReference((TypeReference) child);
                case 2:
                    list3 = x.getVariableSpecifications();
                    if (list3 == null) {
                        aSTArrayList2 = new ASTArrayList();
                        x.setVariableSpecifications(aSTArrayList2);
                    }
                    aSTArrayList2.add(index, child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof MethodDeclaration) {
            ASTList<DeclarationSpecifier> list;
            ASTArrayList aSTArrayList1;
            ASTList<ParameterDeclaration> list2;
            ASTArrayList aSTArrayList2;
            ASTList<TypeParameterDeclaration> list3;
            ASTArrayList aSTArrayList3;
            MethodDeclaration x = (MethodDeclaration) parent;
            switch (role) {
                case 0:
                    list = x.getDeclarationSpecifiers();
                    if (list == null) {
                        aSTArrayList1 = new ASTArrayList();
                        x.setDeclarationSpecifiers(aSTArrayList1);
                    }
                    aSTArrayList1.add(index, child);
                case 1:
                    x.setTypeReference((TypeReference) child);
                case 2:
                    x.setIdentifier((Identifier) child);
                case 3:
                    list2 = x.getParameters();
                    if (list2 == null) {
                        aSTArrayList2 = new ASTArrayList();
                        x.setParameters(aSTArrayList2);
                    }
                    aSTArrayList2.add(index, child);
                case 4:
                    x.setThrown((Throws) child);
                case 5:
                    x.setBody((StatementBlock) child);
                case 7:
                    list3 = x.getTypeParameters();
                    if (list3 == null) {
                        aSTArrayList3 = new ASTArrayList();
                        x.setTypeParameters(aSTArrayList3);
                    }
                    aSTArrayList3.add(index, child);
                case 8:
                    if (x instanceof AnnotationPropertyDeclaration)
                        ((AnnotationPropertyDeclaration) x).setDefaultValue((Expression) child);
                    break;
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof ParameterDeclaration) {
            ASTList<DeclarationSpecifier> list;
            ASTArrayList aSTArrayList;
            ParameterDeclaration x = (ParameterDeclaration) parent;
            switch (role) {
                case 0:
                    list = x.getDeclarationSpecifiers();
                    if (list == null) {
                        aSTArrayList = new ASTArrayList();
                        x.setDeclarationSpecifiers(aSTArrayList);
                    }
                    aSTArrayList.add(index, child);
                case 1:
                    x.setTypeReference((TypeReference) child);
                case 2:
                    x.setVariableSpecification((VariableSpecification) child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof Throws) {
            ASTArrayList aSTArrayList;
            Throws x = (Throws) parent;
            ASTList<TypeReference> list = x.getExceptions();
            if (list == null) {
                aSTArrayList = new ASTArrayList();
                x.setExceptions(aSTArrayList);
            }
            aSTArrayList.add(index, child);
        }
        if (parent instanceof VariableSpecification) {
            VariableSpecification x = (VariableSpecification) parent;
            switch (role) {
                case 0:
                    x.setIdentifier((Identifier) child);
                case 1:
                    x.setInitializer((Expression) child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof ArrayInitializer) {
            ASTArrayList aSTArrayList;
            ArrayInitializer x = (ArrayInitializer) parent;
            ASTList<Expression> list = x.getArguments();
            if (list == null) {
                aSTArrayList = new ASTArrayList();
                x.setArguments(aSTArrayList);
            }
            aSTArrayList.add(index, child);
        }
        if (parent instanceof Operator) {
            Operator x = (Operator) parent;
            if (role == 0) {
                ASTArrayList aSTArrayList;
                ASTList<Expression> list = x.getArguments();
                if (list == null) {
                    aSTArrayList = new ASTArrayList();
                    x.setArguments(aSTArrayList);
                }
                aSTArrayList.add(index, child);
            }
            if (parent instanceof TypeOperator) {
                if (parent instanceof New) {
                    TreeChange result;
                    New new_ = (New) parent;
                    switch (role) {
                        case 0:
                            result = new AttachChange(child);
                            return result;
                        case 1:
                            new_.setTypeReference((TypeReference) child);
                        case 2:
                            new_.setReferencePrefix((ReferencePrefix) child);
                        case 3:
                            new_.setClassDeclaration((ClassDeclaration) child);
                    }
                    throw new IllegalChangeReportException("Illegal child role in " + dc);
                }
                if (parent instanceof NewArray) {
                    NewArray newArray = (NewArray) parent;
                    switch (role) {
                        case 0:

                        case 1:
                            newArray.setTypeReference((TypeReference) child);
                        case 3:
                            newArray.setArrayInitializer((ArrayInitializer) child);
                    }
                    throw new IllegalChangeReportException("Illegal child role in " + dc);
                }
                TypeOperator y = (TypeOperator) parent;
                switch (role) {
                    case 0:

                    case 1:
                        y.setTypeReference((TypeReference) child);
                }
                throw new IllegalChangeReportException("Illegal child role in " + dc);
            }
        }
        if (parent instanceof ArrayLengthReference) {
            ArrayLengthReference x = (ArrayLengthReference) parent;
            x.setReferencePrefix((ReferencePrefix) child);
        }
        if (parent instanceof ArrayReference) {
            ASTList<Expression> list;
            ASTArrayList aSTArrayList;
            ArrayReference x = (ArrayReference) parent;
            switch (role) {
                case 0:
                    x.setReferencePrefix((ReferencePrefix) child);
                case 1:
                    list = x.getDimensionExpressions();
                    if (list == null) {
                        aSTArrayList = new ASTArrayList();
                        x.setDimensionExpressions(aSTArrayList);
                    }
                    aSTArrayList.add(index, child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof FieldReference) {
            FieldReference x = (FieldReference) parent;
            switch (role) {
                case 0:
                    x.setReferencePrefix((ReferencePrefix) child);
                case 1:
                    x.setIdentifier((Identifier) child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof VariableReference) {
            VariableReference x = (VariableReference) parent;
            x.setIdentifier((Identifier) child);
        }
        if (parent instanceof MetaClassReference) {
            MetaClassReference x = (MetaClassReference) parent;
            x.setReferencePrefix((ReferencePrefix) child);
        }
        if (parent instanceof MethodReference) {
            ASTList<Expression> list;
            ASTArrayList aSTArrayList1;
            ASTList<TypeArgumentDeclaration> list2;
            ASTArrayList aSTArrayList2;
            MethodReference x = (MethodReference) parent;
            switch (role) {
                case 0:
                    x.setReferencePrefix((ReferencePrefix) child);
                case 1:
                    x.setIdentifier((Identifier) child);
                case 2:
                    list = x.getArguments();
                    if (list == null) {
                        aSTArrayList1 = new ASTArrayList();
                        x.setArguments(aSTArrayList1);
                    }
                    aSTArrayList1.add(index, child);
                case 3:
                    list2 = x.getTypeArguments();
                    if (list2 == null) {
                        aSTArrayList2 = new ASTArrayList();
                        x.setTypeArguments(aSTArrayList2);
                    }
                    aSTArrayList2.add(index, child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof TypeReferenceInfix) {
            TypeReferenceInfix x = (TypeReferenceInfix) parent;
            switch (role) {
                case 0:
                    x.setReferencePrefix((ReferencePrefix) child);
                case 1:
                    x.setIdentifier((Identifier) child);
                case 2:
                    if (x instanceof TypeReference) {
                        ASTArrayList aSTArrayList;
                        TypeReference y = (TypeReference) x;
                        ASTList<TypeArgumentDeclaration> list2 = y.getTypeArguments();
                        if (list2 == null) {
                            aSTArrayList = new ASTArrayList();
                            y.setTypeArguments(aSTArrayList);
                        }
                        aSTArrayList.add(index, child);
                    }
                    if (x instanceof UncollatedReferenceQualifier) {
                        ASTArrayList aSTArrayList;
                        UncollatedReferenceQualifier y = (UncollatedReferenceQualifier) x;
                        ASTList<TypeArgumentDeclaration> list2 = y.getTypeArguments();
                        if (list2 == null) {
                            aSTArrayList = new ASTArrayList();
                            y.setTypeArguments(aSTArrayList);
                        }
                        aSTArrayList.add(index, child);
                    }
                    break;
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof EnumConstructorReference) {
            ASTList<Expression> list;
            ASTArrayList aSTArrayList;
            EnumConstructorReference x = (EnumConstructorReference) parent;
            switch (role) {
                case 0:
                    x.setClassDeclaration((ClassDeclaration) child);
                case 1:
                    list = x.getArguments();
                    if (list == null) {
                        aSTArrayList = new ASTArrayList();
                        x.setArguments(aSTArrayList);
                    }
                    aSTArrayList.add(index, child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof SuperConstructorReference) {
            ASTList<Expression> list;
            ASTArrayList aSTArrayList;
            SuperConstructorReference x = (SuperConstructorReference) parent;
            switch (role) {
                case 0:
                    x.setReferencePrefix((ReferencePrefix) child);
                case 1:
                    list = x.getArguments();
                    if (list == null) {
                        aSTArrayList = new ASTArrayList();
                        x.setArguments(aSTArrayList);
                    }
                    aSTArrayList.add(index, child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof SuperReference) {
            SuperReference x = (SuperReference) parent;
            x.setReferencePrefix((ReferencePrefix) child);
        }
        if (parent instanceof ThisConstructorReference) {
            ASTArrayList aSTArrayList;
            ThisConstructorReference x = (ThisConstructorReference) parent;
            ASTList<Expression> list = x.getArguments();
            if (list == null) {
                aSTArrayList = new ASTArrayList();
                x.setArguments(aSTArrayList);
            }
            aSTArrayList.add(index, child);
        }
        if (parent instanceof ThisReference) {
            ThisReference x = (ThisReference) parent;
            x.setReferencePrefix((ReferencePrefix) child);
        }
        if (parent instanceof LabelJumpStatement) {
            LabelJumpStatement x = (LabelJumpStatement) parent;
            x.setIdentifier((Identifier) child);
        }
        if (parent instanceof Assert) {
            Assert x = (Assert) parent;
            switch (role) {
                case 0:
                    x.setCondition((Expression) child);
                case 1:
                    x.setMessage((Expression) child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof Case) {
            ASTList<Statement> list;
            ASTArrayList aSTArrayList;
            Case x = (Case) parent;
            switch (role) {
                case 0:
                    x.setExpression((Expression) child);
                case 1:
                    list = x.getBody();
                    if (list == null) {
                        aSTArrayList = new ASTArrayList();
                        x.setBody(aSTArrayList);
                    }
                    aSTArrayList.add(index, child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof Catch) {
            Catch x = (Catch) parent;
            switch (role) {
                case 0:
                    x.setParameterDeclaration((ParameterDeclaration) child);
                case 1:
                    x.setBody((Statement) child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof Default) {
            ASTArrayList aSTArrayList;
            Default x = (Default) parent;
            ASTList<Statement> list = x.getBody();
            if (list == null) {
                aSTArrayList = new ASTArrayList();
                x.setBody(aSTArrayList);
            }
            aSTArrayList.add(index, child);
        }
        if (parent instanceof LoopStatement) {
            ASTList<LoopInitializer> list;
            ASTArrayList aSTArrayList1;
            ASTList<Expression> list2;
            ASTArrayList aSTArrayList2;
            LoopStatement x = (LoopStatement) parent;
            switch (role) {
                case 0:
                    list = x.getInitializers();
                    if (list == null) {
                        aSTArrayList1 = new ASTArrayList();
                        x.setInitializers(aSTArrayList1);
                    }
                    aSTArrayList1.add(index, child);
                case 1:
                    x.setGuard((Expression) child);
                case 2:
                    list2 = x.getUpdates();
                    if (list2 == null) {
                        aSTArrayList2 = new ASTArrayList();
                        x.setUpdates(aSTArrayList2);
                    }
                    aSTArrayList2.add(index, child);
                case 3:
                    x.setBody((Statement) child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof Else) {
            Else x = (Else) parent;
            x.setBody((Statement) child);
        }
        if (parent instanceof Finally) {
            Finally x = (Finally) parent;
            x.setBody((Statement) child);
        }
        if (parent instanceof If) {
            If x = (If) parent;
            switch (role) {
                case 0:
                    x.setExpression((Expression) child);
                case 1:
                    x.setThen((Then) child);
                case 2:
                    x.setElse((Else) child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof LabeledStatement) {
            LabeledStatement x = (LabeledStatement) parent;
            switch (role) {
                case 0:
                    x.setIdentifier((Identifier) child);
                case 1:
                    x.setBody((Statement) child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof ExpressionJumpStatement) {
            ExpressionJumpStatement x = (ExpressionJumpStatement) parent;
            x.setExpression((Expression) child);
        }
        if (parent instanceof Switch) {
            ASTList<Branch> list;
            ASTArrayList aSTArrayList;
            Switch x = (Switch) parent;
            switch (role) {
                case 0:
                    x.setExpression((Expression) child);
                case 1:
                    list = x.getBranchList();
                    if (list == null) {
                        aSTArrayList = new ASTArrayList();
                        x.setBranchList(aSTArrayList);
                    }
                    aSTArrayList.add(index, child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof SynchronizedBlock) {
            SynchronizedBlock x = (SynchronizedBlock) parent;
            switch (role) {
                case 0:
                    x.setExpression((Expression) child);
                case 1:
                    x.setBody((StatementBlock) child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof Then) {
            Then x = (Then) parent;
            x.setBody((Statement) child);
        }
        if (parent instanceof Try) {
            ASTList<Branch> list;
            ASTArrayList aSTArrayList;
            Try x = (Try) parent;
            switch (role) {
                case 0:
                    x.setBody((StatementBlock) child);
                case 1:
                    list = x.getBranchList();
                    if (list == null) {
                        aSTArrayList = new ASTArrayList();
                        x.setBranchList(aSTArrayList);
                    }
                    aSTArrayList.add(index, child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof AnnotationUseSpecification) {
            ASTList<AnnotationElementValuePair> list;
            ASTArrayList aSTArrayList;
            AnnotationUseSpecification x = (AnnotationUseSpecification) parent;
            switch (role) {
                case 0:
                    x.setTypeReference((TypeReference) child);
                case 1:
                    list = x.getElementValuePairs();
                    if (list == null) {
                        aSTArrayList = new ASTArrayList();
                        x.setElementValuePairs(aSTArrayList);
                    }
                    aSTArrayList.add(index, child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof AnnotationElementValuePair) {
            AnnotationElementValuePair x = (AnnotationElementValuePair) parent;
            switch (role) {
                case 0:
                    x.setElement((AnnotationPropertyReference) child);
                case 1:
                    x.setElementValue((Expression) child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof TypeArgumentDeclaration) {
            TypeArgumentDeclaration x = (TypeArgumentDeclaration) parent;
            x.setTypeReference((TypeReference) child);
        }
        if (parent instanceof TypeParameterDeclaration) {
            ASTList<TypeReference> list;
            ASTArrayList aSTArrayList;
            TypeParameterDeclaration x = (TypeParameterDeclaration) parent;
            switch (role) {
                case 0:
                    x.setIdentifier((Identifier) child);
                case 1:
                    list = x.getBounds();
                    if (list == null) {
                        aSTArrayList = new ASTArrayList();
                        x.setBound(aSTArrayList);
                    }
                    aSTArrayList.add(index, child);
            }
            throw new IllegalChangeReportException("Illegal child role in " + dc);
        }
        if (parent instanceof AnnotationPropertyReference) {
            AnnotationPropertyReference x = (AnnotationPropertyReference) parent;
            x.setIdentifier((Identifier) child);
        }
        throw new IllegalChangeReportException("Unknown parent type in " + dc);
    }
}
