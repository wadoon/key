/*
 * Created on 25.11.2005
 *
 * This file is part of the RECODER library and protected by the LGPL.
 * 
 */
package recoder.bytecode;

import java.util.List;

import recoder.ModelException;
import recoder.abstraction.AnnotationUse;
import recoder.abstraction.ArrayType;
import recoder.abstraction.ClassType;
import recoder.abstraction.ClassTypeContainer;
import recoder.abstraction.Constructor;
import recoder.abstraction.ErasedType;
import recoder.abstraction.Field;
import recoder.abstraction.Method;
import recoder.abstraction.Package;
import recoder.abstraction.TypeParameter;
import recoder.convenience.Naming;
import recoder.service.ProgramModelInfo;

/**
 * @author Tobias Gutzmann
 *
 */
public class TypeParameterInfo implements TypeParameter, ClassType {
	private String name;
	
	private String boundNames[];
	
	private List<TypeArgumentInfo> boundArgs[]; 
	
	private ClassFile containingClassFile;
	
	private ArrayType arrayType;
	/**
	 * 
	 */
	public TypeParameterInfo(String name, String[] boundNames, List<TypeArgumentInfo> boundArgs[], ClassFile containingClassFile) {
		super();
		this.name = name.intern();
		this.boundNames = boundNames;
		this.boundArgs = boundArgs;
		this.containingClassFile = containingClassFile;
	}
	
    public ArrayType getArrayType() {
    	return arrayType;
    }
    
    public ArrayType createArrayType() {
    	if (arrayType == null)
    		arrayType = new ArrayType(this, containingClassFile.getProgramModelInfo().getServiceConfiguration().getImplicitElementInfo());
    	return arrayType;
    }

	/* (non-Javadoc)
	 * @see recoder.abstraction.ProgramModelElement#getFullName()
	 */
	public String getFullName() {
		return Naming.dot(containingClassFile.getFullName(), name);
	}
	
	public String getBinaryName() {
		return getContainingClassType().getBinaryName() + "." + getName();
	}


	/* (non-Javadoc)
	 * @see recoder.abstraction.ProgramModelElement#getProgramModelInfo()
	 */
	public ProgramModelInfo getProgramModelInfo() {
		return containingClassFile.getProgramModelInfo();
	}

	/* (non-Javadoc)
	 * @see recoder.abstraction.ProgramModelElement#setProgramModelInfo(recoder.service.ProgramModelInfo)
	 */
	public void setProgramModelInfo(ProgramModelInfo pmi) {
		throw new UnsupportedOperationException(pmi.getClass().getName() + " should not be set for TypeParamterInfo");
	}

	/* (non-Javadoc)
	 * @see recoder.NamedModelElement#getName()
	 */
	public String getName() {
		return name;
	}

	/* (non-Javadoc)
	 * @see recoder.ModelElement#validate()
	 */
	public void validate() throws ModelException {
		// nothing to do
	}

	public String getParameterName() {
		return name;
	}

	public int getBoundCount() {
		return boundNames.length; // never null as java.lang.Object is mandatory
	}

	public String getBoundName(int boundidx) {
		return boundNames[boundidx];
	}

	public List<TypeArgumentInfo> getBoundTypeArguments(int boundidx) {
		return boundArgs[boundidx];
	}
	
	public boolean inheritanceEqual(TypeParameter o) {
		return TypeParameter.EqualsImplementor.equals(this, o);
	}
	
	@Override
	public int hashCode() {
		return containingClassFile.hashCode() ^ name.hashCode();
	}

	public boolean isInterface() {
		return false;
	}

	public boolean isOrdinaryInterface() {
		return false;
	}

	public boolean isAnnotationType() {
		return false;
	}

	public boolean isEnumType() {
		return false;
	}

	public boolean isOrdinaryClass() {
		return false;
	}

	public boolean isAbstract() {
		return false;
	}

	public List<ClassType> getSupertypes() {
		return containingClassFile.getProgramModelInfo().getSupertypes(this);
	}

	public List<ClassType> getAllSupertypes() {
		return containingClassFile.getProgramModelInfo().getAllSupertypes(this);
	}

	public List<FieldInfo> getFields() {
		return null;
	}

	public List<Field> getAllFields() {
		return null;
	}

	public List<Method> getMethods() {
		return null;
	}

	public List<Method> getAllMethods() {
		return containingClassFile.getProgramModelInfo().getAllMethods(this);
	}

	public List<Constructor> getConstructors() {
		return null;
	}

	public List<ClassType> getAllTypes() {
		return null;
	}

	public List<? extends TypeParameter> getTypeParameters() {
		return null;
	}

	public boolean isFinal() {
		return false;
	}

	public boolean isStatic() {
		return false;
	}

	public boolean isPrivate() {
		return false;
	}

	public boolean isProtected() {
		return false;
	}

	public boolean isPublic() {
		// we think this should be ok...
		return true;
	}

	public boolean isStrictFp() {
		return false;
	}

	public ClassType getContainingClassType() {
		return containingClassFile;
	}

	public List<? extends AnnotationUse> getAnnotations() {
		// no annotations possible
		return null;
	}

	public List<ClassType> getTypes() {
		return null;
	}

	public Package getPackage() {
		return containingClassFile.getPackage();
	}

	public ClassTypeContainer getContainer() {
		return containingClassFile;
	}

	// TODO 0.90
	public String getFullSignature() {
		return TypeParameter.DescrImp.getFullSignature(this);
	}
	
	private ErasedType erasedType = null;
	
	public ErasedType getErasedType() {
		if (erasedType == null)
			erasedType = new ErasedType(this, containingClassFile.service.getServiceConfiguration().getImplicitElementInfo());
		return erasedType;
	}

	public boolean isInner() {
		return false;
	}

	@Override
	public String toString() {
		return getFullName();
	}
}
