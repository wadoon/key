package recoder.kit;

import recoder.ProgramFactory;
import recoder.ServiceConfiguration;
import recoder.abstraction.*;
import recoder.convenience.TreeWalker;
import recoder.java.Identifier;
import recoder.java.NamedProgramElement;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.VariableDeclaration;
import recoder.java.declaration.VariableSpecification;
import recoder.java.reference.FieldReference;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.TypeReference;
import recoder.java.reference.VariableReference;
import recoder.service.ChangeHistory;
import recoder.service.CrossReferenceSourceInfo;
import recoder.service.NameInfo;
import recoder.service.SourceInfo;
import recoder.util.Debug;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class VariableKit {
    public static String createValidVariableName(SourceInfo si, ProgramElement context, String guess) {
        Debug.assertNonnull(si, context, guess);
        String result = guess;
        int i = 0;
        Set<String> vars = collectInnerVariables(context);
        while (si.getVariable(result, context) != null || vars.contains(result))
            result = guess + i++;
        return result;
    }

    public static String createValidVariableName(SourceInfo si, ProgramElement context) {
        return createValidVariableName(si, context, "_hvar_");
    }

    public static VariableDeclaration createVariableDeclaration(ServiceConfiguration sc, ProgramElement context, Type t, String guess) {
        Debug.assertNonnull(sc, context, t);
        String vname = createValidVariableName(sc.getSourceInfo(), context, guess);
        ProgramFactory pf = sc.getProgramFactory();
        TypeReference prefix = TypeKit.createTypeReference(pf, t);
        Identifier id = pf.createIdentifier(vname);
        return pf.createLocalVariableDeclaration(prefix, id);
    }

    public static VariableDeclaration createVariableDeclaration(ServiceConfiguration sc, ProgramElement context, Type t) {
        Debug.assertNonnull(sc, context, t);
        String varName = getNewVariableName(sc.getSourceInfo(), t, context);
        ProgramFactory f = sc.getProgramFactory();
        TypeReference prefix = TypeKit.createTypeReference(f, t);
        Identifier id = f.createIdentifier(varName);
        return f.createLocalVariableDeclaration(prefix, id);
    }

    public static VariableReference createVariableReference(VariableDeclaration decl) {
        ProgramFactory factory = decl.getFactory();
        String n = decl.getVariables().get(0).getName();
        return factory.createVariableReference(factory.createIdentifier(n));
    }

    private static Set<String> collectInnerVariables(ProgramElement context) {
        NonTerminalProgramElement nonTerminalProgramElement;
        Set<String> result = new HashSet<String>();
        while (context != null && !(context instanceof recoder.java.VariableScope))
            nonTerminalProgramElement = context.getASTParent();
        if (nonTerminalProgramElement != null) {
            TreeWalker tw = new TreeWalker(nonTerminalProgramElement);
            while (tw.next()) {
                if (tw.getProgramElement() instanceof Variable)
                    result.add(((Variable) tw.getProgramElement()).getName());
            }
        }
        return result;
    }

    public static String getNewVariableName(SourceInfo si, Type type, ProgramElement context) {
        Debug.assertNonnull(si, type, context);
        NameGenerator generator = new NameGenerator(type);
        Set<String> vars = collectInnerVariables(context);
        String result;
        for (result = generator.getNextCandidate(); si.getVariable(result, context) != null || vars.contains(result); result = generator.getNextCandidate())
            ;
        return result;
    }

    public static String[] getNewVariableNames(SourceInfo si, Type[] types, ProgramElement context) {
        NonTerminalProgramElement nonTerminalProgramElement;
        Debug.assertNonnull(si, types, context);
        while (!(context instanceof recoder.java.VariableScope))
            nonTerminalProgramElement = context.getASTParent();
        Set<String> others = collectInnerVariables(nonTerminalProgramElement);
        String[] results = new String[types.length];
        for (int i = 0; i < results.length; i++) {
            NameGenerator generator = new NameGenerator(types[i]);
            while (true) {
                String vname = generator.getNextCandidate();
                if (si.getVariable(vname, nonTerminalProgramElement) == null && !others.contains(vname)) {
                    results[i] = vname;
                    others.add(vname);
                    break;
                }
            }
        }
        return results;
    }

    public static boolean rename(ChangeHistory ch, CrossReferenceSourceInfo xr, VariableSpecification var, String newName) {
        Debug.assertNonnull(xr, var, newName);
        Debug.assertNonnull(var.getName());
        if (!newName.equals(var.getName())) {
            List<? extends VariableReference> refs = xr.getReferences(var);
            MiscKit.rename(ch, var, newName);
            for (int i = refs.size() - 1; i >= 0; i--)
                MiscKit.rename(ch, refs.get(i), newName);
            return true;
        }
        return false;
    }

    public static VariableReference createVariableReference(SourceInfo si, Variable v, ProgramElement context) {
        Debug.assertNonnull(si, v, context);
        String varname = v.getName();
        ProgramFactory f = context.getFactory();
        Variable lookup = si.getVariable(varname, context);
        if (lookup == null)
            return null;
        if (lookup == v) {
            VariableReference res = f.createVariableReference(f.createIdentifier(varname));
            res.makeAllParentRolesValid();
            return res;
        }
        if (!(v instanceof Field))
            return null;
        ClassType varClass = ((Field) v).getContainingClassType();
        TypeDeclaration ctxClass = MiscKit.getParentTypeDeclaration(context);
        TypeReference prefix = null;
        do {
            if (varClass == ctxClass) {
                FieldReference res = f.createFieldReference(f.createIdentifier(varname));
                res.setReferencePrefix(f.createThisReference(prefix));
                res.makeAllParentRolesValid();
                return res;
            }
            List<ClassType> sups = ctxClass.getAllSupertypes();
            int i, s;
            label32:
            for (i = 1, s = sups.size(); i < s; i++) {
                ClassType sup = sups.get(i);
                List<? extends Field> flist = sup.getFields();
                for (int j = 0, t = flist.size(); j < t; j++) {
                    Field candid = flist.get(j);
                    if (varname.equals(candid.getName())) {
                        if (candid == v) {
                            if (si.isVisibleFor(candid, ctxClass)) {
                                FieldReference res = f.createFieldReference(f.createIdentifier(varname));
                                res.setReferencePrefix(f.createSuperReference(prefix));
                                res.makeAllParentRolesValid();
                                return res;
                            }
                            break label32;
                        }
                        break label32;
                    }
                }
            }
            ctxClass = ctxClass.getMemberParent();
            if (ctxClass == null)
                continue;
            prefix = TypeKit.createTypeReference(si, ctxClass, context);
        } while (ctxClass != null);
        return null;
    }

    public static List<VariableReference> getReferences(CrossReferenceSourceInfo xr, Variable v, NonTerminalProgramElement root, boolean scanTree) {
        Debug.assertNonnull(xr, v, root);
        List<VariableReference> result = new ArrayList<VariableReference>();
        if (scanTree) {
            TreeWalker tw = new TreeWalker(root);
            while (tw.next(VariableReference.class)) {
                VariableReference vr = (VariableReference) tw.getProgramElement();
                if (xr.getVariable(vr) == v)
                    result.add(vr);
            }
        } else {
            List<? extends VariableReference> refs = xr.getReferences(v);
            for (int i = 0, s = refs.size(); i < s; i++) {
                VariableReference vr = refs.get(i);
                if (MiscKit.contains(root, vr))
                    result.add(vr);
            }
        }
        return result;
    }

    public static boolean isSerialVersionUID(NameInfo ni, Field f) {
        return (f.isStatic() && f.isFinal() && f.getType() == ni.getLongType() && f.getName().equals("serialVersionUID"));
    }
}
