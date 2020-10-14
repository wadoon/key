/*
 * Created on 27.11.2005
 *
 * This file is part of the RECODER library and protected by the LGPL.
 * 
 */
package recoder.bytecode;

import java.util.List;

import recoder.abstraction.TypeArgument;
import recoder.abstraction.TypeParameter;

/**
 * 
 * @author Tobias Gutzmann
 *
 */
public class TypeArgumentInfo implements TypeArgument {
	final WildcardMode wildcardMode;
	private final String typeName;
	final List<? extends TypeArgument> typeArgs;
	final boolean isTypeVariable;
	ByteCodeElement parent;
	/**
	 * 
	 */
	public TypeArgumentInfo(WildcardMode wildcardMode, String typeName, List<? extends TypeArgument> typeArgs, ByteCodeElement parent, boolean isTypeVariable) {
		super();
		if ((typeName == null && wildcardMode != WildcardMode.Any) || wildcardMode == null || parent == null) throw new NullPointerException();
		this.wildcardMode = wildcardMode;
		if (typeName != null)
			this.typeName = typeName.intern();
		else
			this.typeName = null;
		this.typeArgs = typeArgs;
		this.isTypeVariable = isTypeVariable;
		this.parent = parent;
	}
	public WildcardMode getWildcardMode() {
		return wildcardMode;
	}
	public String getTypeName() {
		return typeName;
	}
	public List<? extends TypeArgument> getTypeArguments() {
		return typeArgs;
	}
	public boolean isTypeVariable() {
		return isTypeVariable;
	}
	public ClassFile getContainingClassFile() {
		if (parent instanceof ClassFile)
			return (ClassFile)parent;
		else return (ClassFile)((MethodInfo)parent).getContainingClassType();
	}
	public MethodInfo getContainingMethodInfo() {
		if (parent instanceof MethodInfo)
			return (MethodInfo)parent;
		return null;
	}
	
//	public boolean equals(Object o) {
//		if (o instanceof TypeArgument)
//			return TypeArgument.EqualsImpl.equals(this, (TypeArgument)o);
//		return false;
//	}
	
	public boolean semanticalEquality(TypeArgument ta) {
		return TypeArgument.EqualsImpl.equals(this, ta);
	}
	
	public TypeParameter getTargetedTypeParameter() {
		// TODO 0.90
		throw new RuntimeException("TODO");
	}

    public String getFullSignature() {
    	return TypeArgument.DescriptionImpl.getFullDescription(this);
    }

}
