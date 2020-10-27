package recoder.bytecode;

import recoder.abstraction.Field;
import recoder.abstraction.Type;
import recoder.convenience.Naming;

import java.util.List;

public class FieldInfo extends MemberInfo implements Field {
    protected String type;

    protected String constantValue;

    protected List<TypeArgumentInfo> typeArgs;

    public FieldInfo(int accessFlags, String name, String type, ClassFile cf, String constantValue, List<TypeArgumentInfo> typeArgs) {
        super(accessFlags, name, cf);
        this.type = type;
        this.constantValue = constantValue;
        this.typeArgs = typeArgs;
    }

    public final String getTypeName() {
        return this.type;
    }

    public final String getConstantValue() {
        return this.constantValue;
    }

    public Type getType() {
        return this.service.getType(this);
    }

    public String getFullName() {
        return Naming.getFullName(this);
    }

    public List<TypeArgumentInfo> getTypeArguments() {
        return this.typeArgs;
    }
}
