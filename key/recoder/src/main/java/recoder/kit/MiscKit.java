package recoder.kit;

import recoder.ProgramFactory;
import recoder.convenience.TreeWalker;
import recoder.java.*;
import recoder.java.declaration.MemberDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.UncollatedReferenceQualifier;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.ChangeHistory;
import recoder.util.Debug;

import java.util.Map;

public class MiscKit {
    public static UncollatedReferenceQualifier createUncollatedReferenceQualifier(ProgramFactory factory, String name) {
        UncollatedReferenceQualifier result = null;
        int j = -1;
        while (true) {
            int i = j + 1;
            j = name.indexOf(".", i);
            String token = (j > i) ? name.substring(i, j) : name.substring(i);
            result = factory.createUncollatedReferenceQualifier(result, factory.createIdentifier(token));
            if (j <= i) {
                result.makeAllParentRolesValid();
                return result;
            }
        }
    }

    public static boolean contains(NonTerminalProgramElement root, ProgramElement node) {
        if (root == null)
            return false;
        while (node != null) {
            if (node == root)
                return true;
            NonTerminalProgramElement nonTerminalProgramElement = node.getASTParent();
        }
        return false;
    }

    public static void setName(NamedProgramElement e, String name) {
        if (!name.equals(e.getName()))
            Transformation.doAttach(e.getFactory().createIdentifier(name), e);
    }

    public static Identifier rename(ChangeHistory ch, NamedProgramElement namedElement, String newName) {
        Debug.assertNonnull(namedElement, newName);
        Identifier oldId = namedElement.getIdentifier();
        if (!newName.equals(oldId.getText())) {
            Identifier newId = namedElement.getFactory().createIdentifier(newName);
            namedElement.setIdentifier(newId);
            newId.setParent(namedElement);
            if (ch != null)
                ch.replaced(oldId, newId);
            return newId;
        }
        return oldId;
    }

    public static CompilationUnit getParentCompilationUnit(ProgramElement pe) {
        return UnitKit.getCompilationUnit(pe);
    }

    public static TypeDeclaration getParentTypeDeclaration(ProgramElement pe) {
        NonTerminalProgramElement nonTerminalProgramElement;
        do {
            nonTerminalProgramElement = pe.getASTParent();
        } while (nonTerminalProgramElement != null && !(nonTerminalProgramElement instanceof TypeDeclaration));
        return (TypeDeclaration) nonTerminalProgramElement;
    }

    public static ScopeDefiningElement getScopeDefiningElement(ProgramElement pe) {
        NonTerminalProgramElement nonTerminalProgramElement;
        while (!(pe instanceof ScopeDefiningElement))
            nonTerminalProgramElement = pe.getASTParent();
        return (ScopeDefiningElement) nonTerminalProgramElement;
    }

    public static MemberDeclaration getParentMemberDeclaration(ProgramElement pe) {
        NonTerminalProgramElement nonTerminalProgramElement;
        do {
            nonTerminalProgramElement = pe.getASTParent();
        } while (nonTerminalProgramElement != null && !(nonTerminalProgramElement instanceof MemberDeclaration));
        return (MemberDeclaration) nonTerminalProgramElement;
    }

    public static ProgramElement checkParentLinks(ProgramElement root) {
        if (root instanceof NonTerminalProgramElement) {
            NonTerminalProgramElement nt = (NonTerminalProgramElement) root;
            for (int s = nt.getChildCount(), i = 0; i < s; i++) {
                ProgramElement child = nt.getChildAt(i);
                if (child.getASTParent() != nt)
                    return child;
                child = checkParentLinks(child);
                if (child != null)
                    return child;
            }
        }
        return null;
    }

    public static void remove(ChangeHistory ch, ProgramElement child) {
        Debug.assertNonnull(child);
        if (child instanceof CompilationUnit) {
            if (ch != null)
                ch.detached(child, 0);
        } else {
            NonTerminalProgramElement parent = child.getASTParent();
            Debug.assertNonnull(parent);
            int oldIndex = parent.getChildPositionCode(child);
            parent.replaceChild(child, null);
            if (ch != null)
                ch.detached(child, parent, oldIndex);
        }
    }

    public static void replace(ChangeHistory ch, ProgramElement child, ProgramElement replacement) {
        Debug.assertNonnull(child, replacement);
        if (child != replacement) {
            if (!(child instanceof CompilationUnit)) {
                NonTerminalProgramElement parent = child.getASTParent();
                parent.replaceChild(child, replacement);
            }
            if (ch != null)
                ch.replaced(child, replacement);
        }
    }

    private static void add(ChangeHistory ch, CompilationUnit parent, Import child, boolean asHead) {
        Debug.assertNonnull(parent, child);
        ASTList<Import> list = parent.getImports();
        if (list == null) {
            parent.setImports(new ASTArrayList(child));
        } else if (asHead) {
            list.add(0, child);
        } else {
            list.add(child);
        }
        child.setParent(parent);
        if (ch != null)
            ch.attached(child);
    }

    public static void append(ChangeHistory ch, CompilationUnit parent, Import child) {
        add(ch, parent, child, false);
    }

    public static void prepend(ChangeHistory ch, CompilationUnit parent, Import child) {
        add(ch, parent, child, true);
    }

    private static void add(ChangeHistory ch, StatementBlock parent, Statement child, boolean asHead) {
        Debug.assertNonnull(parent, child);
        ASTList<Statement> list = parent.getBody();
        if (list == null) {
            parent.setBody(new ASTArrayList(child));
        } else if (asHead) {
            list.add(0, child);
        } else {
            list.add(child);
        }
        child.setStatementContainer(parent);
        if (ch != null)
            ch.attached(child);
    }

    public static void append(ChangeHistory ch, StatementBlock parent, Statement child) {
        add(ch, parent, child, false);
    }

    public static void prepend(ChangeHistory ch, StatementBlock parent, Statement child) {
        add(ch, parent, child, true);
    }

    public static void unindent(ProgramElement root) {
        TreeWalker w = new TreeWalker(root);
        SourceElement.Position undef = SourceElement.Position.UNDEFINED;
        while (w.next()) {
            ProgramElement pe = w.getProgramElement();
            pe.setRelativePosition(undef);
            pe.setStartPosition(undef);
            pe.setEndPosition(undef);
        }
    }

    public static void mapClones(ProgramElement originalRoot, ProgramElement cloneRoot, Map<ProgramElement, ProgramElement> map) {
        Debug.assertNonnull(originalRoot, cloneRoot, map);
        for (TreeWalker w1 = new TreeWalker(originalRoot), w2 = new TreeWalker(cloneRoot); (w1.next() & w2.next()) != 0; map.put(w1.getProgramElement(), w2.getProgramElement()))
            ;
    }

    public static ProgramElement getClone(ProgramElement original, ProgramElement originalRoot, ProgramElement cloneRoot) {
        Debug.assertNonnull(original, originalRoot, cloneRoot);
        TreeWalker w1 = new TreeWalker(originalRoot);
        TreeWalker w2 = new TreeWalker(cloneRoot);
        while ((w1.next() & w2.next()) != 0) {
            if (w1.getProgramElement() == original)
                return w2.getProgramElement();
        }
        return original;
    }
}
