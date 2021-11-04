package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.ReferenceType;
import com.github.javaparser.ast.type.Type;
import de.uka.ilkd.key.java.transformations.ConstantEvaluator;
import de.uka.ilkd.key.java.transformations.EvaluationException;
import de.uka.ilkd.key.util.Debug;

import javax.annotation.Nonnull;
import java.util.Optional;

/**
 * @author Alexander Weigl
 * @version 1 (11/2/21)
 */
public class TransformationPipelineServices {
    @Nonnull
    private final TransformerCache cache;

    public TransformationPipelineServices(@Nonnull TransformerCache cache) {
        this.cache = cache;
    }

    @Nonnull
    public TransformerCache getCache() {
        return cache;
    }

    public ConstantEvaluator getConstantEvaluator() {
        return new ConstantEvaluator();
    }


    protected TypeDeclaration<?> containingClass(TypeDeclaration<?> td) {
        Node container = td.getContainingReferenceType();
        if (container == null) {
            container = td.getParentNode().get();
        }
        while (!(container instanceof TypeDeclaration<?>)) {
            container = container.getParentNode().get();
        }
        return (TypeDeclaration<?>) container;
    }


    public String getId(TypeDeclaration td) {
        if (td.getIdentifier() != null) {
            return td.getIdentifier().clone();
        }

        final ReferenceType firstActualSupertype = getAllSupertypes(td).get(1);
        return firstActualSupertype instanceof TypeDeclaration ?
                getId((TypeDeclaration) firstActualSupertype) :
                new Identifier(firstActualSupertype.getName());

    }

    protected MethodDeclaration containingMethod(TypeDeclaration td) {
        Node container = td.getParentNode().get();
        while (container != null && !(container instanceof MethodDeclaration)) {
            container = container.getParentNode().get();
        }
        return (MethodDeclaration) container;
    }


    /**
     * returns the default value of the given type
     * according to JLS Sect. 4.5.5
     *
     * @return the default value of the given type
     * according to JLS Sect. 4.5.5
     */
    public Expression getDefaultValue(Type type) {
        if (type instanceof ReferenceType) {
            return new NullLiteralExpr();
        } else if (type instanceof PrimitiveType) {
            PrimitiveType ptype = (PrimitiveType) type;
            switch (ptype.getType()) {
                case BOOLEAN:
                    return new BooleanLiteralExpr(false);
                case KEY_BIGINT:
                case BYTE:
                case SHORT:
                case INT:
                    return new IntegerLiteralExpr("0");
                case LONG:
                    return new LongLiteralExpr("0");

                case CHAR:
                    return new CharLiteralExpr((char) 0);
                case FLOAT:
                case DOUBLE:
                case KEY_REAL:
                    return new DoubleLiteralExpr("0.0");

                case KEY_LOCSET:
                case KEY_SEQ:
                case KEY_FREE:
                case KEY_MAP:
                    throw new IllegalArgumentException("TODO");
                    //return new KeyEscapeExpression(null, new NodeList<>());
            }
        }
        Debug.fail("makeImplicitMembersExplicit: unknown primitive type" + type);
        return null;
    }

    public Type getType(Expression n) {
        return null;
    }

    public ClassOrInterfaceType getType(String... names) {
        ClassOrInterfaceType type = null;
        for (String name : names) {
            type = new ClassOrInterfaceType(type, name);
        }
        return type;
    }

    public Name getName(String... names) {
        Name type = null;
        for (String name : names) {
            type = new Name(type, name);
        }
        return type;
    }

    /**
     * returns true if the given FieldDeclaration denotes a constant
     * field. A constant field is declared as final and static and
     * initialised with a time constant, which is not prepared or
     * initialised here.  ATTENTION: this is a derivation from the JLS
     * but the obtained behaviour is equivalent as we only consider
     * completely compiled programs and not partial compilations. The
     * reason for preparation and initialisation of comnpile time
     * constant fields is due to binary compatibility reasons.
     */
    private boolean isConstant(Expression expr) {
        ConstantEvaluator ce = getConstantEvaluator();
        try {
            return ce.isCompileTimeConstant(expr);
        } catch (EvaluationException e) {
            e.printStackTrace();
            return false;
        }
    }

    public boolean isConstant(Optional<Expression> initializer) {
        return initializer.map(this::isConstant).orElse(false);
    }
}
