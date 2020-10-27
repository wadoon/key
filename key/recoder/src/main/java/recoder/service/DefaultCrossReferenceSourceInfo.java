package recoder.service;

import recoder.ModelElement;
import recoder.ServiceConfiguration;
import recoder.abstraction.Package;
import recoder.abstraction.*;
import recoder.convenience.Format;
import recoder.convenience.TreeWalker;
import recoder.io.SourceFileRepository;
import recoder.java.CompilationUnit;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.Reference;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.InheritanceSpecification;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.expression.operator.New;
import recoder.java.reference.*;
import recoder.util.Debug;
import recoder.util.ProgressEvent;

import java.util.*;

public class DefaultCrossReferenceSourceInfo extends DefaultSourceInfo implements CrossReferenceSourceInfo {
    private final Map<ProgramModelElement, Set<Reference>> element2references = new HashMap<ProgramModelElement, Set<Reference>>(256);

    public DefaultCrossReferenceSourceInfo(ServiceConfiguration config) {
        super(config);
    }

    public void modelChanged(ChangeHistoryEvent changes) {
        List<TreeChange> changed = changes.getChanges();
        int s = changed.size();
        int c = 0;
        this.listeners.fireProgressEvent(0, 3 * s, "Building Scopes");
        int i;
        for (i = 0; i < s; i++) {
            TreeChange tc = changed.get(i);
            if (tc instanceof DetachChange) {
                if (!tc.isMinor())
                    processChange(tc);
                this.listeners.fireProgressEvent(++c);
            }
        }
        for (i = 0; i < s; i++) {
            TreeChange tc = changed.get(i);
            if (tc instanceof AttachChange) {
                if (!tc.isMinor())
                    processChange(tc);
                this.listeners.fireProgressEvent(++c);
            }
        }
        this.listeners.fireProgressEvent(c, "Resolving References");
        TreeWalker tw = new TreeWalker(null);
        int j;
        for (j = 0; j < s; j++) {
            TreeChange tc = changed.get(j);
            if (tc instanceof DetachChange) {
                if (!tc.isMinor()) {
                    ProgramElement pe = tc.getChangeRoot();
                    boolean rippleEffect = isPossiblyShowingRippleEffect(tc);
                    if (pe instanceof recoder.java.declaration.TypeArgumentDeclaration) {
                        reset(true);
                        return;
                    }
                    if (pe instanceof Reference) {
                        if (!rippleEffect) {
                            deregisterReference((Reference) pe);
                        } else {
                            reset(true);
                            return;
                        }
                    } else {
                        if (pe instanceof ProgramModelElement || pe instanceof recoder.java.declaration.VariableDeclaration) {
                            reset(true);
                            return;
                        }
                        if (pe instanceof InheritanceSpecification) {
                            reset(true);
                            return;
                        }
                        if (pe instanceof recoder.java.declaration.AnnotationElementValuePair) {
                            reset(true);
                            return;
                        }
                    }
                    tw.reset(pe);
                    tw.next();
                    while (tw.next()) {
                        ProgramElement p = tw.getProgramElement();
                        if (p instanceof Reference)
                            deregisterReference((Reference) p);
                    }
                }
                this.listeners.fireProgressEvent(++c);
            }
        }
        for (j = 0; j < s; j++) {
            TreeChange tc = changed.get(j);
            if (tc instanceof AttachChange) {
                if (!tc.isMinor()) {
                    ProgramElement pe = tc.getChangeRoot();
                    NonTerminalProgramElement pa = tc.getChangeRootParent();
                    if (pe instanceof recoder.java.declaration.TypeArgumentDeclaration) {
                        reset(true);
                        return;
                    }
                    if (pe instanceof Reference) {
                        if (!(pe instanceof recoder.java.Expression) || isPossiblyShowingRippleEffect(tc)) {
                            reset(true);
                            return;
                        }
                    } else {
                        if (pe instanceof ProgramModelElement || pe instanceof recoder.java.declaration.VariableDeclaration) {
                            reset(true);
                            return;
                        }
                        if (pe instanceof InheritanceSpecification) {
                            reset(true);
                            return;
                        }
                        if (pe instanceof recoder.java.declaration.AnnotationElementValuePair) {
                            reset(true);
                            return;
                        }
                    }
                }
                this.listeners.fireProgressEvent(++c);
            }
        }
        for (j = 0; j < s; j++) {
            TreeChange tc = changed.get(j);
            if (!tc.isMinor() && tc instanceof AttachChange) {
                AttachChange ac = (AttachChange) tc;
                ProgramElement pe = ac.getChangeRoot();
                analyzeReferences(pe);
            }
            this.listeners.fireProgressEvent(++c);
        }
    }

    private boolean isPossiblyShowingRippleEffect(TreeChange tc) {
        return true;
    }

    public List<MemberReference> getReferences(Method m) {
        Debug.assertNonnull(m);
        updateModel();
        Set references = this.element2references.get(m);
        if (references == null)
            return new ArrayList<MemberReference>(0);
        int s = references.size();
        if (s == 0)
            return new ArrayList<MemberReference>(0);
        List<MemberReference> result = new ArrayList<MemberReference>(s);
        for (Object o : references)
            result.add((MemberReference) o);
        return result;
    }

    public List<ConstructorReference> getReferences(Constructor c) {
        Debug.assertNonnull(c);
        updateModel();
        Set<Reference> references = this.element2references.get(c);
        if (references == null)
            return new ArrayList<ConstructorReference>(0);
        int s = references.size();
        if (s == 0)
            return new ArrayList<ConstructorReference>(0);
        List<ConstructorReference> result = new ArrayList<ConstructorReference>(s);
        for (Reference o : references)
            result.add((ConstructorReference) o);
        return result;
    }

    public List<VariableReference> getReferences(Variable v) {
        Debug.assertNonnull(v);
        updateModel();
        Set references = this.element2references.get(v);
        if (references == null)
            return new ArrayList<VariableReference>(0);
        int s = references.size();
        if (s == 0)
            return new ArrayList<VariableReference>(0);
        List<VariableReference> result = new ArrayList<VariableReference>(s);
        for (Object o : references)
            result.add((VariableReference) o);
        return result;
    }

    public List<FieldReference> getReferences(Field f) {
        Debug.assertNonnull(f);
        updateModel();
        Set references = this.element2references.get(f);
        if (references == null)
            return new ArrayList<FieldReference>(0);
        int s = references.size();
        if (s == 0)
            return new ArrayList<FieldReference>(0);
        List<FieldReference> result = new ArrayList<FieldReference>(s);
        for (Object o : references)
            result.add((FieldReference) o);
        return result;
    }

    public List<TypeReference> getReferences(Type t) {
        Debug.assertNonnull(t);
        updateModel();
        Set<Reference> references = this.element2references.get(t);
        if (references == null)
            return new ArrayList<TypeReference>(0);
        int s = references.size();
        if (s == 0)
            return new ArrayList<TypeReference>(0);
        List<TypeReference> result = new ArrayList<TypeReference>(s);
        for (Reference r : references)
            result.add((TypeReference) r);
        return result;
    }

    public List<PackageReference> getReferences(Package p) {
        Debug.assertNonnull(p);
        updateModel();
        Set<Reference> references = this.element2references.get(p);
        if (references == null)
            return new ArrayList<PackageReference>(0);
        int s = references.size();
        if (s == 0)
            return new ArrayList<PackageReference>(0);
        List<PackageReference> result = new ArrayList<PackageReference>(s);
        for (Reference pr : references)
            result.add((PackageReference) pr);
        return result;
    }

    private void registerReference(Reference ref, ProgramModelElement pme) {
        Set<Reference> set = this.element2references.get(pme);
        if (set == null)
            this.element2references.put(pme, set = new HashSet<Reference>(4));
        set.add(ref);
    }

    private void deregisterReference(Reference ref) {
        ProgramModelElement pme = this.reference2element.get(ref);
        if (pme == null)
            return;
        Set set = this.element2references.get(pme);
        if (set == null)
            return;
        set.remove(ref);
    }

    private void analyzeReferences(ProgramElement pe) {
        if (pe instanceof NonTerminalProgramElement) {
            NonTerminalProgramElement nt = (NonTerminalProgramElement) pe;
            for (int i = 0, c = nt.getChildCount(); i < c; i++)
                analyzeReferences(nt.getChildAt(i));
        } else {
            return;
        }
        if (pe instanceof Reference) {
            Reference reference;
            if (pe instanceof UncollatedReferenceQualifier)
                try {
                    reference = resolveURQ((UncollatedReferenceQualifier) pe);
                } catch (ClassCastException cce) {
                    getErrorHandler().reportError(new UnresolvedReferenceException(Format.toString("Could not resolve %c \"%s\" @%p in %f", reference), reference));
                }
            if (reference instanceof VariableReference) {
                Field field;
                VariableReference vr = (VariableReference) reference;
                Variable v = getVariable(vr);
                if (v == null) {
                    getErrorHandler().reportError(new UnresolvedReferenceException(Format.toString("Could not resolve %c \"%s\" @%p in %f", vr), vr));
                    field = getNameInfo().getUnknownField();
                }
                registerReference(vr, field);
            } else if (reference instanceof TypeReference) {
                ClassType classType;
                TypeReference tr = (TypeReference) reference;
                Type t = getType(tr);
                if (t instanceof ParameterizedType)
                    classType = ((ParameterizedType) t).getGenericType();
                if (classType != null &&
                        !(classType instanceof DefaultNameInfo.UnknownClassType)) {
                    registerReference(tr, classType);
                    if (classType instanceof ClassType) {
                        ClassDeclaration classDeclaration;
                        ClassType subType = null;
                        TypeReferenceContainer parent = tr.getParent();
                        if (parent instanceof InheritanceSpecification) {
                            TypeDeclaration typeDeclaration = ((InheritanceSpecification) parent).getParent();
                        } else if (parent instanceof New) {
                            classDeclaration = ((New) parent).getClassDeclaration();
                        }
                        if (classDeclaration != null) {
                            ClassType superType = classType;
                            ProgramModelInfo pmi = superType.getProgramModelInfo();
                            ((DefaultProgramModelInfo) pmi).registerSubtype(classDeclaration, superType);
                        }
                    }
                }
            } else if (reference instanceof MethodReference) {
                MethodReference mr = (MethodReference) reference;
                Method m = getMethod(mr);
                registerReference(mr, m);
            } else if (reference instanceof ConstructorReference) {
                ConstructorReference cr = (ConstructorReference) reference;
                Constructor c = getConstructor(cr);
                registerReference(cr, c);
            } else if (reference instanceof AnnotationPropertyReference) {
                AnnotationPropertyReference apr = (AnnotationPropertyReference) reference;
                AnnotationProperty ap = getAnnotationProperty(apr);
                registerReference(apr, ap);
            } else if (reference instanceof PackageReference) {
                PackageReference pr = (PackageReference) reference;
                Package p = getPackage(pr);
                registerReference(pr, p);
            }
        }
    }

    public String information() {
        updateModel();
        int c1 = 0, c2 = 0, c3 = 0, c4 = 0, c5 = 0;
        int r1 = 0, r2 = 0, r3 = 0, r4 = 0, r5 = 0;
        for (ProgramModelElement pme : this.element2references.keySet()) {
            Set set = this.element2references.get(pme);
            int size = (set == null) ? 0 : set.size();
            if (pme instanceof Variable) {
                c1++;
                r1 += size;
                continue;
            }
            if (pme instanceof Method) {
                if (pme instanceof Constructor) {
                    c3++;
                    r3 += size;
                    continue;
                }
                c2++;
                r2 += size;
                continue;
            }
            if (pme instanceof Type) {
                c4++;
                r4 += size;
                continue;
            }
            if (pme instanceof Package) {
                c5++;
                r5 += size;
            }
        }
        return "" + c1 + " variables with " + r1 + " references\n" + c2 + " methods with " + r2 + " references\n" + c3 + " constructors with " + r3 + " references\n" + c4 + " types with " + r4 + " references\n" + c5 + " packages with " + r5 + " references";
    }

    private void reset(boolean fire) {
        super.reset();
        this.element2references.clear();
        SourceFileRepository sfr = this.serviceConfiguration.getSourceFileRepository();
        List<CompilationUnit> cul = sfr.getCompilationUnits();
        int c = 0;
        if (fire) {
            ProgressEvent pe = this.listeners.getLastProgressEvent();
            c = pe.getWorkDoneCount();
            this.listeners.fireProgressEvent(c, c + cul.size());
        }
        for (int i = cul.size() - 1; i >= 0; i--) {
            CompilationUnit cu = cul.get(i);
            analyzeReferences(cu);
            if (fire)
                this.listeners.fireProgressEvent(++c);
        }
    }

    public void reset() {
        reset(false);
    }

    class SubTypeTopSort extends ClassTypeTopSort {
        protected final List<ClassType> getAdjacent(ClassType c) {
            return DefaultCrossReferenceSourceInfo.this.getSubtypes(c);
        }
    }
}
