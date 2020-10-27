package recoder.bytecode;

import recoder.abstraction.ClassTypeContainer;
import recoder.abstraction.Constructor;
import recoder.convenience.Naming;

public class ConstructorInfo extends MethodInfo implements Constructor {
    public ConstructorInfo(int accessFlags, String name, String[] paramtypes, String[] exceptions, ClassFile cf) {
        super(accessFlags, null, name, paramtypes, exceptions, cf);
    }

    public String getFullName() {
        return Naming.getFullName(this);
    }
}
