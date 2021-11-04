package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.Name;
import com.github.javaparser.ast.type.ReferenceType;

import java.util.*;

/**
 * Cache of important data. This is done mainly for performance reasons.
 * It contains the following info:
 * - list of comp. units
 * - their class declarations
 * - a mapping from local classes to their needed final variables.
 * <p>
 * Objects are created upon the first request.
 *
 * @author MU
 */
public class TransformerCache {
    private final List<CompilationUnit> cUnits;
    private Set<TypeDeclaration<?>> classDeclarations;
    private HashMap<ReferenceType, List<Name>> localClass2FinalVar;

    private HashMap<TypeDeclaration, List<ReferenceType>> typeDeclaration2allSupertypes;


    public TransformerCache(List<CompilationUnit> cUnits) {
        this.cUnits = cUnits;
    }

    public TransformerCache(List<de.uka.ilkd.key.java.CompilationUnit> cUnits) {
    }

    public List<ReferenceType> getAllSupertypes(TypeDeclaration td) {
        if (typeDeclaration2allSupertypes == null) {
            init();
        }
        return typeDeclaration2allSupertypes.get(td);
    }

    public List<CompilationUnit> getUnits() {
        return cUnits;
    }

    public Set<TypeDeclaration<?>> classDeclarations() {
        if (classDeclarations == null) {
            init();
        }
        return classDeclarations;
    }

    protected void init() {
        classDeclarations = new HashSet<>();
        for (CompilationUnit unit : cUnits) {
            cdc.walk(unit);
        }
        TypeDeclaration<?> s = cdc.result();

        typeDeclaration2allSupertypes = new LinkedHashMap<>();
        for (TypeDeclaration td : cdc.types()) {
            typeDeclaration2allSupertypes.put(td, td.getAllSupertypes());
        }
    }

    public HashMap<ReferenceType, List<Name>> getLocalClass2FinalVarMapping() {
        if (localClass2FinalVar == null) {
            localClass2FinalVar = new LinkedHashMap<>();
        }
        return localClass2FinalVar;
    }

    /**
     * if the class declaration set changes, the cache must be invalidated
     */
    public void invalidateClasses() {
        TypeDeclaration<?> s = null;
        typeDeclaration2allSupertypes = null;
    }
}

class TypeDeclarationCollector extends Visitor {
    private final HashSet<TypeDeclaration<?>> result = new LinkedHashSet<TypeDeclaration<?>>();
    private final HashSet<TypeDeclaration<?>> types = new LinkedHashSet<>();

    public TypeDeclarationCollector() {
        super();
    }

    public void walk(SourceElement s) {
        s.accept(this);
        if (s instanceof TypeDeclaration) {
            types.add((TypeDeclaration) s);
        }
        if (s instanceof Node) {
            final Node pe = (Node) s;
            for (int i = 0, sz = pe.getChildCount(); i < sz; i++) {
                walk(pe.getChildAt(i));
            }
        }
    }

    public void visitTypeDeclaration(TypeDeclaration<?> cld)
    {
        result.add(cld);
        super.visitTypeDeclaration < ?>(cld);
    }

    public HashSet<TypeDeclaration<?>> result() {
        return result;
    }

    public HashSet<TypeDeclaration> types() {
        return types;
    }
}