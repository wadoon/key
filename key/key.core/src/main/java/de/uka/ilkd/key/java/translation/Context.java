// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.translation;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.resolution.SymbolResolver;
import de.uka.ilkd.key.java.api.JavaService;

import java.util.concurrent.atomic.AtomicInteger;

/**
 * this class stores recoder related contextinformation used to parse
 * in program parts in which non-declared variables are used
 */
class Context {
    public static final AtomicInteger CLASS_COUNTER = new AtomicInteger();
    public static final String PARSING_CONTEXT_CLASS_NAME = "$KeYSpecialParsing";
    private final CompilationUnit unit;

    /**
     * creates a new context object
     */
    public Context(CompilationUnit unit) {
        this.unit = unit;
    }

    public static Context createDefault() {
        CompilationUnit unit = new CompilationUnit();
        var type = new ClassOrInterfaceDeclaration(null, false,
                PARSING_CONTEXT_CLASS_NAME + CLASS_COUNTER.getAndIncrement());
        type.addModifier(Modifier.Keyword.PUBLIC);
        unit.addType(type);
        return new Context(unit);
    }

    public static Context createDefault(JavaService service) {
        return createDefault(service.getSymbolResolver());
    }

    private static Context createDefault(SymbolResolver symbolResolver) {
        var context = createDefault();
        JavaService.injectSymbolResolver(context.getCompilationUnitContext(), symbolResolver);
        return context;
    }

    /**
     * returns the compilation context
     */
    public CompilationUnit getCompilationUnitContext() {
        return unit;
    }

    /**
     * returns the compilation context
     */
    public ClassOrInterfaceDeclaration getClassContext() {
        return (ClassOrInterfaceDeclaration) unit.getPrimaryType().get();
    }
}