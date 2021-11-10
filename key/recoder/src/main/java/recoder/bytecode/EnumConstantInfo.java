/**
 * Created on 13.06.2008
 * <p>
 * This file is part of the RECODER library and protected by the LGPL.
 */
package recoder.bytecode;

import recoder.abstraction.EnumConstant;

import java.util.List;

/**
 * @author Tobias Gutzmann
 *
 */
public class EnumConstantInfo extends FieldInfo implements EnumConstant {

    /**
     * @param accessFlags
     * @param name
     * @param type
     * @param cf
     * @param constantValue
     * @param typeArgs
     */
    public EnumConstantInfo(int accessFlags, String name, String type,
                            ClassFile cf, String constantValue, List<TypeArgumentInfo> typeArgs) {
        super(accessFlags, name, type, false, cf, constantValue, typeArgs);
    }

}
