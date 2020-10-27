package recoder.bytecode;

import recoder.abstraction.AnnotationProperty;

public class AnnotationPropertyInfo extends MethodInfo implements AnnotationProperty {
    private final Object defaultValue;

    public AnnotationPropertyInfo(int accessFlags, String returntype, String name, ClassFile cf, Object defaultValue) {
        super(accessFlags, returntype, name, new String[0], new String[0], cf);
        this.defaultValue = defaultValue;
    }

    public Object getDefaultValue() {
        return this.defaultValue;
    }
}
