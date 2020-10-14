/*
 * Created on 23.11.2005
 *
 * This file is part of the RECODER library and protected by the LGPL.
 * 
 */
package recoder.abstraction;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;

import recoder.ModelException;
import recoder.service.ImplicitElementInfo;
import recoder.service.ProgramModelInfo;

/**
 * A parameterized type, meaning a generic type plus actual type arguments.
 * This is for internal representation and not an AST representation element.
 * 
 * @author Tobias Gutzmann
 *
 */
public class ParameterizedType implements ClassType {
	/**
	 * the capture of this parameterized type.
	 * See JLS, 3rd edition, §5.1.10
	 * @author Tobias Gutzmann
	 *
	 */
	public class CapturedType implements ClassType {
		/**
		 * 
		 */
		public CapturedType() {
			// nothing to do, all information provided in ParameterizedType
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassType#getAllFields()
		 */
		public List<Field> getAllFields() {
			// TODO 0.90 check this !? (JLS ??)
			return ParameterizedType.this.getAllFields();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassType#getAllMethods()
		 */
		public List<Method> getAllMethods() {
			// TODO 0.90 check this !? (JLS ??)
			return ParameterizedType.this.getAllMethods();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassType#getAllSupertypes()
		 */
		public List<ClassType> getAllSupertypes() {
			// TODO 0.90 check this !? (JLS ??)
			return ParameterizedType.this.getAllSupertypes();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassType#getAllTypes()
		 */
		public List<ClassType> getAllTypes() {
			// TODO 0.90 check this !? (JLS ??)
			return ParameterizedType.this.getAllTypes();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassType#getConstructors()
		 */
		public List<? extends Constructor> getConstructors() {
			// TODO 0.90 check this !? (JLS ??)
			return ParameterizedType.this.getConstructors();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassType#getErasedType()
		 */
		public ErasedType getErasedType() {
			// TODO 0.90 check this !? (JLS ??)
			return ParameterizedType.this.getErasedType();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassType#getFields()
		 */
		public List<? extends Field> getFields() {
			// TODO 0.90 check this !? (JLS ??)
			return ParameterizedType.this.getFields();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassType#getFullSignature()
		 */
		public String getFullSignature() {
			// TODO 0.90 check this !? (JLS ??)
			return ParameterizedType.this.getFullSignature();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassType#getMethods()
		 */
		public List<Method> getMethods() {
			// TODO 0.90 check this !? (JLS ??)
			return ParameterizedType.this.getMethods();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassType#getSupertypes()
		 */
		public List<ClassType> getSupertypes() {
			// TODO 0.90 check this !? (JLS ??)
			return ParameterizedType.this.getSupertypes();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassType#getTypeParameters()
		 */
		public List<? extends TypeParameter> getTypeParameters() {
			// TODO 0.90 check this !? (JLS ??)
			return ParameterizedType.this.getTypeParameters();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassType#isAbstract()
		 */
		public boolean isAbstract() {
			return ParameterizedType.this.isAbstract();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassType#isAnnotationType()
		 */
		public boolean isAnnotationType() {
			return ParameterizedType.this.isAnnotationType();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassType#isEnumType()
		 */
		public boolean isEnumType() {
			return ParameterizedType.this.isEnumType();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassType#isInner()
		 */
		public boolean isInner() {
			return ParameterizedType.this.isInner();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassType#isInterface()
		 */
		public boolean isInterface() {
			return ParameterizedType.this.isInterface();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassType#isOrdinaryClass()
		 */
		public boolean isOrdinaryClass() {
			return ParameterizedType.this.isOrdinaryClass();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassType#isOrdinaryInterface()
		 */
		public boolean isOrdinaryInterface() {
			return ParameterizedType.this.isOrdinaryInterface();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.Type#createArrayType()
		 */
		public ArrayType createArrayType() {
			// TODO 0.90 !?
			throw new RuntimeException(); 
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.Type#getArrayType()
		 */
		public ArrayType getArrayType() {
			// TODO 0.90 !?
			throw new RuntimeException(); 
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ProgramModelElement#getFullName()
		 */
		public String getFullName() {
			return ParameterizedType.this.getFullName();
		}
		
		public String getBinaryName() {
			return ParameterizedType.this.getBinaryName();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ProgramModelElement#getProgramModelInfo()
		 */
		public ProgramModelInfo getProgramModelInfo() {
			return ParameterizedType.this.getProgramModelInfo();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ProgramModelElement#setProgramModelInfo(recoder.service.ProgramModelInfo)
		 */
		public void setProgramModelInfo(ProgramModelInfo pmi) {
			throw new UnsupportedOperationException();
		}

		/* (non-Javadoc)
		 * @see recoder.NamedModelElement#getName()
		 */
		public String getName() {
			return ParameterizedType.this.getName();
		}

		/* (non-Javadoc)
		 * @see recoder.ModelElement#validate()
		 */
		public void validate() throws ModelException {
			// TODO Auto-generated method stub

		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.Member#getAnnotations()
		 */
		public List<? extends AnnotationUse> getAnnotations() {
			return ParameterizedType.this.getAnnotations();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.Member#getContainingClassType()
		 */
		public ParameterizedType getContainingClassType() {
			return ParameterizedType.this;
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.Member#isFinal()
		 */
		public boolean isFinal() {
			return ParameterizedType.this.isFinal();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.Member#isPrivate()
		 */
		public boolean isPrivate() {
			return ParameterizedType.this.isPrivate();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.Member#isProtected()
		 */
		public boolean isProtected() {
			return ParameterizedType.this.isProtected();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.Member#isPublic()
		 */
		public boolean isPublic() {
			return ParameterizedType.this.isPublic();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.Member#isStatic()
		 */
		public boolean isStatic() {
			return ParameterizedType.this.isStatic();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.Member#isStrictFp()
		 */
		public boolean isStrictFp() {
			return ParameterizedType.this.isStrictFp();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassTypeContainer#getContainer()
		 */
		public ClassTypeContainer getContainer() {
			return ParameterizedType.this;
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassTypeContainer#getPackage()
		 */
		public Package getPackage() {
			return ParameterizedType.this.getPackage();
		}

		/* (non-Javadoc)
		 * @see recoder.abstraction.ClassTypeContainer#getTypes()
		 */
		public List<? extends ClassType> getTypes() {
			// TODO 0.90
			throw new RuntimeException();
		}

	}
	
	private final ClassType genericType;
	private final List<? extends TypeArgument> typeArgs;
	private final ParameterizedType enclosingType;
	
	private ArrayType arrayType;
	private CapturedType capture;
	
	private final ImplicitElementInfo pmi;
	/**
	 * 
	 */
	private ParameterizedType(ClassType genericType, List<? extends TypeArgument> typeArgs,
							 ImplicitElementInfo service) {
		this (genericType, typeArgs, null, service);
	}
	
	private ParameterizedType(ClassType innerGenericType, List<? extends TypeArgument> typeArgs,
			ParameterizedType enclosingType, ImplicitElementInfo service) {
		super();
		if (innerGenericType == null) 
			throw new NullPointerException();
		if (typeArgs == null) 
			typeArgs = Collections.<TypeArgument>emptyList();
		this.genericType = innerGenericType;
		this.typeArgs = typeArgs;
		this.pmi = service;
		this.enclosingType = enclosingType;
		
		assert typeArgs.size() != 0 || enclosingType != null;
		
		// below, the case > can happen if type parameters are taken from an outer class or not type variables at all
//		assert typeArgs.size() >= genericType.getTypeParameters().size();
		// TODO above assert may cause NullPointerException on inner types without own type parameters 
	}
	
	private static HashMap<ParameterizedType,ParameterizedType> ptypes = new HashMap<ParameterizedType,ParameterizedType>(4096);
	
	public static ParameterizedType getParameterizedType(ClassType genericType, List<? extends TypeArgument> typeArgs,
			 ImplicitElementInfo service) {
		return getParameterizedType(genericType, typeArgs, null, service);
	}
	
	public static ParameterizedType getParameterizedType(ClassType innerGenericType, 
		    List<? extends TypeArgument> typeArgs,
			ParameterizedType enclosingType, ImplicitElementInfo service) {
		// TODO this might be improved...
		ParameterizedType newRes = new ParameterizedType(innerGenericType, typeArgs, enclosingType, service);
		ParameterizedType oldRes = ptypes.get(newRes);
		if (oldRes != null)
			return oldRes;
		ptypes.put(newRes, newRes);
		return newRes;
	}
	
	// TODO 0.90 doc / rename ?
	public List<TypeParameter> getDefinedTypeParameters() {
		if (genericType.getTypeParameters() == null)
			return enclosingType.getDefinedTypeParameters(); // this MUST be defined!
		List<TypeParameter> outerTPs = enclosingType == null ? 
				Collections.<TypeParameter>emptyList() : enclosingType.getDefinedTypeParameters();  
		int sz = genericType.getTypeParameters().size() + 
					outerTPs.size();
		List<TypeParameter> res = new ArrayList<TypeParameter>(sz);
		res.addAll(genericType.getTypeParameters());
		res.addAll(outerTPs);
		return res;
	}
	
    public ArrayType getArrayType() {
    	return arrayType;
    }
    
    public ArrayType createArrayType() {
    	if (arrayType == null)
    		arrayType = new ArrayType(this, pmi.getServiceConfiguration().getImplicitElementInfo());
    	return arrayType;
    }
    
    public CapturedType getCapture() {
    	if (capture == null)
    		capture = new CapturedType();
    	return capture;
    }
    
    // TODO 0.90 check references if they shouldn't use getDefinedTypeParameters
	public ClassType getGenericType() {
		return genericType;
	}
	
	public ParameterizedType getEnclosingType() {
		return enclosingType;
	}
	
	private List<TypeArgument> allTypeArgs = null;
	/**
	 * includes the type args of a possibly enclosing type
	 * @return
	 */
	public List<TypeArgument> getAllTypeArgs() {
		if (allTypeArgs != null)
			return allTypeArgs;
		List<TypeArgument> outerArgs = enclosingType == null ? 
				Collections.<TypeArgument>emptyList() : enclosingType.getAllTypeArgs();  
		int sz = typeArgs.size() + 
					outerArgs.size();
		List<TypeArgument> res = new ArrayList<TypeArgument>(sz);
		res.addAll(typeArgs);
		res.addAll(outerArgs);
		allTypeArgs = res;
		return res;
	}
	
	public List<? extends TypeArgument> getTypeArgs() {
		return typeArgs;
	}

	/* (non-Javadoc)
	 * @see recoder.abstraction.ProgramModelElement#getFullName()
	 */
	public String getFullName() {
		return genericType.getFullName();
	}
	
	public String getBinaryName() {
		return genericType.getBinaryName();
	}

	/* (non-Javadoc)
	 * @see recoder.abstraction.ProgramModelElement#getProgramModelInfo()
	 */
	public ImplicitElementInfo getProgramModelInfo() {
		return pmi;
	}

	/**
	 * @throws RuntimeException - not to be called but set by constructor!
	 */
	public void setProgramModelInfo(ProgramModelInfo pmi) {
		throw new RuntimeException("ParameterizedType.setProgramModelInfo must not be called!");
	}

	/* (non-Javadoc)
	 * @see recoder.NamedModelElement#getName()
	 */
	public String getName() {
		return genericType.getName();
	}

	/* (non-Javadoc)
	 * @see recoder.ModelElement#validate()
	 */
	public void validate() throws ModelException {
		// TODO Auto-generated method stub
		
	}

	/**
	 * @return the empty list
	 */
	public List<TypeParameter> getTypeParameters() {
		return Collections.<TypeParameter>emptyList();
	}

	public boolean isInterface() {
		return genericType.isInterface();
	}

	public boolean isOrdinaryInterface() {
		return genericType.isOrdinaryInterface();
	}

	public boolean isAnnotationType() {
		return genericType.isAnnotationType();
	}

	public boolean isEnumType() {
		return genericType.isEnumType();
	}

	public boolean isOrdinaryClass() {
		return genericType.isOrdinaryClass();
	}

	public boolean isAbstract() {
		return genericType.isAbstract();
	}

	public List<ClassType> getSupertypes() {
		return pmi.getSupertypes(this);
	}

	public List<ClassType> getAllSupertypes() {
		return pmi.getAllSupertypes(this);
	}

	public List<? extends Field> getFields() {
		return pmi.getFields(this);
	}

	public List<Field> getAllFields() {
		return pmi.getAllFields(this);
	}

	public List<Method> getMethods() {
		return pmi.getMethods(this);
	}

	public List<Method> getAllMethods() {
		return pmi.getAllMethods(this);
	}

	public List<? extends Constructor> getConstructors() {
		return pmi.getConstructors(this);
	}

	public List<ClassType> getAllTypes() {
		return pmi.getAllTypes(this);
	}

	public boolean isFinal() {
		return genericType.isFinal();
	}

	public boolean isStatic() {
		return genericType.isStatic();
	}

	public boolean isPrivate() {
		return genericType.isPrivate();
	}

	public boolean isProtected() {
		return genericType.isProtected();
	}

	public boolean isPublic() {
		return genericType.isPublic();
	}

	public boolean isStrictFp() {
		return genericType.isStrictFp();
	}

	public ClassType getContainingClassType() {
		// TODO 0.90 !?
		return genericType.getContainingClassType();
	}

	public List<? extends AnnotationUse> getAnnotations() {
		return genericType.getAnnotations();
	}

	public List<? extends ClassType> getTypes() {
		return pmi.getTypes(this);
	}

	public Package getPackage() {
		return genericType.getPackage();
	}

	public ClassTypeContainer getContainer() {
		return genericType.getContainer();
	}

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof ParameterizedType))
			return false;
		ParameterizedType pt = (ParameterizedType)o;
		if (pt == this)
			return true;
		if (pt.pmi != pmi)
			return false; // multiple instances !? TODO look into this...
		if (pt.getGenericType() != getGenericType())
			return false;
		// check type arguments. The two types MUST have the same number of type arguments!
		List<? extends TypeArgument> ta1 = getAllTypeArgs();
		List<? extends TypeArgument> ta2 = pt.getAllTypeArgs();
		if (ta1.size() != ta2.size())
			return false; // scenario: java.util.HashMap<String,String>.HashIterator vs. java.util.HashMap.HashIterator<V> ...
		for (int i = 0; i < ta1.size(); i++) {
			if (!ta1.get(i).semanticalEquality(ta2.get(i)))
				return false;
		}
		return true;
	}
	
	@Override
	public int hashCode() {
		// TODO 0.90 improve !!!
		return genericType.hashCode();
	}
	
    // TODO 0.90
    public String getFullSignature() {
    	String res;
    	if (enclosingType != null)
    		res = enclosingType.getFullSignature() + "." + getName();
    	else 
    		res = getFullName();
    	if (typeArgs.size() == 0) return res;
    	else res += "<";
    	String del = "";
    	for (TypeArgument ta : getTypeArgs()) {
    		res = res + del + ta.getFullSignature();
    		del = ",";
    	}
    	res = res + ">";
    	return res;
    }
    
    @Override
    public String toString() {
    	return getFullSignature();
    }
    
	public ErasedType getErasedType() {
		return getGenericType().getErasedType();
	}

	public boolean isInner() {
		return genericType.isInner();
	}
}
