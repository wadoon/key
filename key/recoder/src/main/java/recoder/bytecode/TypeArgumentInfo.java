package recoder.bytecode;

import recoder.abstraction.TypeArgument;

import java.util.List;

public class TypeArgumentInfo implements TypeArgument {
    final TypeArgument.WildcardMode wildcardMode;

    final String typeName;

    final List<? extends TypeArgument> typeArgs;

    final boolean isTypeVariable;

    ByteCodeElement parent;

    public TypeArgumentInfo(TypeArgument.WildcardMode wildcardMode, String typeName, List<? extends TypeArgument> typeArgs, ByteCodeElement parent, boolean isTypeVariable) {
        if ((typeName == null && wildcardMode != TypeArgument.WildcardMode.Any) || wildcardMode == null || parent == null)
            throw new NullPointerException();
        this.wildcardMode = wildcardMode;
        this.typeName = typeName;
        this.typeArgs = typeArgs;
        this.isTypeVariable = isTypeVariable;
        this.parent = parent;
    }

    public TypeArgument.WildcardMode getWildcardMode() {
        return this.wildcardMode;
    }

    public String getTypeName() {
        return this.typeName;
    }

    public List<? extends TypeArgument> getTypeArguments() {
        return this.typeArgs;
    }

    public boolean isTypeVariable() {
        return this.isTypeVariable;
    }

    public ClassFile getContainingClassFile() {
        if (this.parent instanceof ClassFile)
            return (ClassFile) this.parent;
        return (ClassFile) ((MethodInfo) this.parent).getContainingClassType();
    }

    public MethodInfo getContainingMethodInfo() {
        if (this.parent instanceof MethodInfo)
            return (MethodInfo) this.parent;
        return null;
    }
}
