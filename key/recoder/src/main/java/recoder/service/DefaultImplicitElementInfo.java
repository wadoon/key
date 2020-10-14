// This file is part of the RECODER library and protected by the LGPL.

package recoder.service;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import recoder.ServiceConfiguration;
import recoder.abstraction.ArrayType;
import recoder.abstraction.ClassType;
import recoder.abstraction.ClassTypeContainer;
import recoder.abstraction.Constructor;
import recoder.abstraction.DefaultConstructor;
import recoder.abstraction.ErasedConstructor;
import recoder.abstraction.ErasedField;
import recoder.abstraction.ErasedMethod;
import recoder.abstraction.ErasedType;
import recoder.abstraction.Field;
import recoder.abstraction.ImplicitEnumMethod;
import recoder.abstraction.ImplicitEnumValueOf;
import recoder.abstraction.ImplicitEnumValues;
import recoder.abstraction.IntersectionType;
import recoder.abstraction.Member;
import recoder.abstraction.Method;
import recoder.abstraction.NullType;
import recoder.abstraction.Package;
import recoder.abstraction.ParameterizedConstructor;
import recoder.abstraction.ParameterizedField;
import recoder.abstraction.ParameterizedMethod;
import recoder.abstraction.ParameterizedType;
import recoder.abstraction.PrimitiveType;
import recoder.abstraction.ProgramModelElement;
import recoder.abstraction.ResolvedGenericMethod;
import recoder.abstraction.Type;
import recoder.abstraction.TypeArgument;
import recoder.abstraction.ArrayType.ArrayCloneMethod;
import recoder.abstraction.TypeArgument.CapturedTypeArgument;
import recoder.abstraction.TypeArgument.WildcardMode;
import recoder.java.declaration.EnumDeclaration;
import recoder.util.Debug;

/**
 * Handles requests for implicitly defined program model elements. In
 * particular these are {@link recoder.abstraction.NullType},
 * {@link recoder.abstraction.Package},{@link recoder.abstraction.ArrayType},
 * {@link recoder.abstraction.DefaultConstructor},
 * {@link recoder.abstraction.ImplicitEnumValueOf},
 * {@link recoder.abstraction.ImplicitEnumValues},
 * and {@link recoder.abstraction.IntersectionType}.
 * TODO 0.90 should be more by now...
 */
public class DefaultImplicitElementInfo extends DefaultProgramModelInfo implements ImplicitElementInfo {

    /** maps type declarations to default constructors */
    private final Map<ClassType, DefaultConstructor> type2defaultConstructor = new HashMap<ClassType, DefaultConstructor>();
    
    private final Map<EnumDeclaration,List<ImplicitEnumMethod>> type2implicitEnumMethods = new HashMap<EnumDeclaration,List<ImplicitEnumMethod>>();

    /**
     * @param config
     *            the configuration this services becomes part of.
     */
    public DefaultImplicitElementInfo(ServiceConfiguration config) {
        super(config);
    }

    public DefaultConstructor getDefaultConstructor(ClassType ct) {
        Debug.assertNonnull(ct);
        updateModel();
        DefaultConstructor cons = type2defaultConstructor.get(ct);
        if (cons == null) {
            cons = new DefaultConstructor(ct);
            cons.setProgramModelInfo(this);
            type2defaultConstructor.put(ct, cons);
        }
        return cons;
    }
    
    public List<ImplicitEnumMethod> getImplicitEnumMethods(EnumDeclaration etd) {
    	if (etd == null) throw new NullPointerException();
    	updateModel();
    	List<ImplicitEnumMethod> res = type2implicitEnumMethods.get(etd);
    	if (res == null) {
    		res = new ArrayList<ImplicitEnumMethod>(2);
    		ImplicitEnumMethod meth = new ImplicitEnumValueOf(etd);
    		meth.setProgramModelInfo(this);
    		res.add(meth);
    		meth = new ImplicitEnumValues(etd);
    		meth.setProgramModelInfo(this);
    		res.add(meth);
    		type2implicitEnumMethods.put(etd, res);
    	}
    	return res;
    }
    
    public Type getType(ProgramModelElement pme) {
        if (pme instanceof NullType 
        		|| pme instanceof ArrayType 
        		|| pme instanceof IntersectionType
        		|| pme instanceof ErasedType
        		|| pme instanceof CapturedTypeArgument) {
            return (Type) pme;
        } else if (pme instanceof Package) {
            // valid for Package
            return null; 
        } else if (pme instanceof ErasedField) {
        	// TODO 0.90
        	return eraseType(((ErasedField)pme).getGenericField().getType());
        } else if (pme instanceof ParameterizedField) {
        	ParameterizedField pf = (ParameterizedField)pme;
    		Type genRet = pf.getGenericField().getType();
    		
    		return replaceAllTypeParametersWithArgs(genRet, 
    				pf.getContainingClassType().getDefinedTypeParameters(), 
    				pf.getContainingClassType().getAllTypeArgs());
        } else {
        	return getReturnType((Method)pme);
        }
    }

    public Package getPackage(ProgramModelElement pme) {
        if (pme instanceof Package) {
            return (Package) pme;
        }
        if (pme instanceof DefaultConstructor || pme instanceof ImplicitEnumMethod) {
            updateModel();
            return getContainingClassType((Method) pme).getPackage();
        }
        // TODO 0.90 valid for ... ?
        return null;
    }

    public List<? extends ClassType> getTypes(ClassTypeContainer ctc) {
        if (ctc instanceof Package) {
            return serviceConfiguration.getNameInfo().getTypes((Package) ctc);
        }
        if (ctc instanceof DefaultConstructor) {
            return new ArrayList<ClassType>(0);
        }
        if (ctc instanceof ErasedMethod) {
        	// TODO 0.90
        	throw new RuntimeException();
        }
        if (ctc instanceof ErasedType) {
        	return eraseTypes(((ErasedType)ctc).getGenericType().getTypes());
        }
        if (ctc instanceof ParameterizedType) {
        	ParameterizedType pt = (ParameterizedType)ctc;
        	List<? extends ClassType> genericTypes = pt.getGenericType().getTypes();
        	ArrayList<ClassType> res = new ArrayList<ClassType>(genericTypes.size());
        	for (ClassType ct : genericTypes) {
        		if (ct.isInner())
            		// TODO 0.90 
        			res.add(ParameterizedType.getParameterizedType(ct, null, (ParameterizedType)ctc, this));
        		else
        			res.add(ct);
        	}
        	return res;
        }
        if (ctc instanceof ResolvedGenericMethod) {
        	// TODO 0.90
        	throw new RuntimeException();
        }
        // TODO 0.90 valid for ... ?
        return null;
    }

    public List<ClassType> getAllTypes(ClassType ct) {
    	if (ct instanceof ParameterizedType)
    		throw new RuntimeException("TODO");
        // valid for NullType, ArrayType
    	assert ct == getNameInfo().getNullType()
    			|| ct instanceof ArrayType;
        return null;
    }

    public ClassTypeContainer getClassTypeContainer(ClassType ct) {
        // valid for NullType
    	assert ct == getNameInfo().getNullType();
        return null;
    }
    
    private ClassType makeParentParameterizedType(ParameterizedType subType, ClassType st) {
    	if (!(st instanceof ParameterizedType))
    		return st;
    	ParameterizedType superType = (ParameterizedType)st;

    	ClassType res = replaceAllTypeParametersWithArgs(superType,
    			subType.getDefinedTypeParameters(), subType.getAllTypeArgs());
    	
    	return res;
    	
//    	List<TypeParameter> tps = new ArrayList<TypeParameter>();
//    	tps.addAll(subType.getTypeParameters());
//    	List<TypeArgument> targs = new ArrayList<TypeArgument>();
//    	targs.addAll(superType.getTypeArgs());
//    	if (subType.getEnclosingType() != null) {
//    		
//    	}
    	
    	
//    	ClassType res = replaceAllTypeParametersWithArgs(superType.getGenericType(), 
//    				subType.getTypeParameters(),
//    				superType.getAllTypeArgs());
    	
//    	if (subType.getEnclosingType() != null)
//    		res = replaceAllTypeParametersWithArgs(res, subType.getEnclosingType().getDefinedTypeParameters(), 
//    				subType.getEnclosingType().getTypeArgs());
//
//    	return res;
//    	List<? extends TypeArgument> typeArgs 
//    						= replaceTypeArgsRec(subType, superType.getTypeArgs());
//    	return new ParameterizedType(superType.getGenericType(), typeArgs, this);
    }

    public List<ClassType> getSupertypes(ClassType ct) {
    	if (ct instanceof IntersectionType) {
    		return ((IntersectionType)ct).getSupertypes();
    	}
    	if (ct instanceof ParameterizedType) {
    		// Test: are all type arguments non-wildcard types ?
    		ParameterizedType pt = (ParameterizedType)ct;
    		List<? extends TypeArgument> typeArgs = pt.getAllTypeArgs();
    		boolean allNonWildcard = true;
    		for (TypeArgument ta : typeArgs) {
    			if (ta.getWildcardMode() != WildcardMode.None) {
    				allNonWildcard = false;
    				break;
    			}
    		}
    		if (!allNonWildcard) {
    			// Perform capture conversion, JLS 3rd edtion §5.1.10
//    		 TODO 0.90 !!!
    		}
    		// TODO MOST IMPORTANT
//    		if (allNonWildcard) {
				ArrayList<ClassType> res = new ArrayList<ClassType>();
				res.add(pt.getGenericType().getErasedType());
    			List<ClassType> genericSupers = pt.getGenericType().getSupertypes();
    			for (ClassType genSuper : genericSupers) {
    				res.add(makeParentParameterizedType(pt, genSuper));
    			}
    			return res;
//    		} else {
//    			// TODO 0.90
//    			return pt.getGenericType().getSupertypes();
//    		}
    	}
    	if (ct instanceof ErasedType) {
    		ErasedType rt = (ErasedType)ct;
    		List<ClassType> genericSupers = rt.getGenericType().getSupertypes();
    		ArrayList<ClassType> res = new ArrayList<ClassType>(genericSupers.size());
    		for (ClassType sup : genericSupers) {
    			if (sup instanceof ParameterizedType)
    				sup = ((ParameterizedType)sup).getGenericType(); // cf. JLS 3rd edition, §4.8 TODO 0.90 testcase!
    			res.add(sup.getErasedType());
    		}
    		return res;
    	}
    	if (ct instanceof NullType)
    		// actually, every reference type there is... JLS 3rd edition, §4.10.2,
    		// but we handle null explicitly in Recoder
    		return null;
    	if (ct instanceof ArrayType) {
    		/* JLS 3rd edition, § 4.10.3 lists the rules for 
    		 * direct subtyping among array types:
    		 * (1) S and T reference types, T direct subtype of S -> T[] direct subtype of S[]
    		 * (2) Object[] direct subtype of Object, Cloneable, and java.io.Serializable
    		 * (3) if p is a primitive type:
    		 *     p[] direct subtype of Object, Cloneable, java.io.Serializable
    		 * 
    		 */
    		ArrayList<ClassType> res = new ArrayList<ClassType>();
    		NameInfo ni = getNameInfo();
    		ArrayType at = (ArrayType)ct;    		
    		Type baseType = at.getBaseType();
    		if (baseType instanceof PrimitiveType || baseType == ni.getJavaLangObject()) {
    			// rule 2 + 3
    			res.add(ni.getJavaIoSerializable());
    			res.add(ni.getJavaLangCloneable());
    			res.add(ni.getJavaLangObject());
    		} else {
    			// rule 1
    			List<ClassType> baseTypesSupers = ((ClassType)baseType).getSupertypes();
    			for (ClassType sup : baseTypesSupers) {
    				res.add(ni.createArrayType(sup));
    			}
    		}
    		return res;
    	}
    	if (ct instanceof CapturedTypeArgument) {
    		CapturedTypeArgument cta = (CapturedTypeArgument)ct;
    		TypeArgument ta = cta.getTypeArgument();
    		if (ta.getWildcardMode() == WildcardMode.Any
    				|| ta.getWildcardMode() == WildcardMode.Super) {
        		// TODO 0.90 fix "? super T"-handling, this is just a hack for now!!
        		return ta.getTargetedTypeParameter().getSupertypes();
    		}
    		// TODO 0.90 ?
    		return getBaseType(ta).getSupertypes();
    	}
    		
    	return ct.getProgramModelInfo().getSupertypes(ct); 
    }

    public List<ClassType> getAllSupertypes(ClassType ct) {
    	ProgramModelInfo pmi = ct.getProgramModelInfo();
    	if (pmi != this)
    		return pmi.getAllSupertypes(ct);
        if (ct instanceof ParameterizedType || ct instanceof ArrayType
        		|| ct instanceof IntersectionType || ct instanceof ErasedType
        		|| ct instanceof CapturedTypeArgument)
        	return super.getAllSupertypes(ct);
        if (ct instanceof NullType) {
        	List<ClassType> result = new ArrayList<ClassType>(1);
        	result.add(ct);
            return result;
        }
        // must not be reached
        throw new RuntimeException("DefaultImplicitElementInfo not a valid service for " + ct.getClass().getName());
    }

    public List<? extends Field> getFields(ClassType ct) {
    	if (ct instanceof ParameterizedType) {
    		ParameterizedType pt = (ParameterizedType)ct;
    		List<? extends Field> temp = pt.getGenericType().getFields();
    		List<Field> res = new ArrayList<Field>(temp.size());
    		for (Field f : temp) {
    			if (getServiceConfiguration().getSourceInfo().containsTypeParameter(f))
    				res.add(new ParameterizedField(f, pt, this));
    			else 
    				res.add(f);
    		}
    		return res;
    	}
    	if (ct instanceof ArrayType) {
    		ArrayType at = (ArrayType)ct;
    		ArrayList<Field> res = new ArrayList<Field>(1);
    		res.add(at.getArrayLengthField());
    		return res;
    	}
    	if (ct instanceof ErasedType) {
    		ErasedType et = (ErasedType)ct;
    		List<? extends Field> genericFields = et.getGenericType().getFields();
    		ArrayList<Field> res = new ArrayList<Field>(genericFields.size());
    		for (Field f : genericFields) {
    			// TODO 0.90 do not create erased field if not a type variable or parameterized 
    			if (f.isStatic()) {
    				res.add(f);
    			} else {
    				res.add(new ErasedField(f, this));
    			}
    		}
    		return res;
    	}
    	if (ct instanceof CapturedTypeArgument) {
    		// TODO 0.90
    		throw new RuntimeException("TODO");
    	}

        // valid for NullType
    	assert ct == getNameInfo().getNullType();
        return null;
    }

    public List<Field> getAllFields(ClassType ct) {
        // valid for NullType
    	if (ct instanceof IntersectionType 
    		|| ct instanceof ParameterizedType 
    		|| ct instanceof ArrayType
    		|| ct instanceof ErasedType
    		|| ct instanceof CapturedTypeArgument)
    		return super.getAllFields(ct);
        return null;
    }

    public List<Method> getMethods(ClassType ct) {
        // valid for NullType and ParameterizedType
    	if (ct instanceof ParameterizedType) {
    		ParameterizedType pt = (ParameterizedType)ct;
    		List<Method> temp = pt.getGenericType().getMethods();
    		List<Method> res = new ArrayList<Method>(temp.size());
    		for (Method m : temp) {
    			Method pm = m;
    			if (getServiceConfiguration().getSourceInfo().containsTypeParameter(m))
    				pm = new ParameterizedMethod(m, pt, this);

    			// TODO 0.90 handling somewhere else ?
    			// check: is return type an inner type?
    			Type ret = m.getReturnType(); 
    			if (ret instanceof ClassType && ((ClassType)ret).isInner()) {
    				// TODO 0.92 need to carry over type parameters from ct to m now... But how ?
    				//ClassType cc = (ClassType)ret;
    			}
    			res.add(pm);
    		}
    		return res;
    	}
    	if (ct instanceof ArrayType) {
    		ArrayList<Method> res = new ArrayList<Method>(2);
    		ArrayType at = (ArrayType)ct;
    		res.add(at.getArrayCloneMethod());
    		return res;
    	}
    	if (ct instanceof ErasedType) {
    		ErasedType et = (ErasedType)ct;
    		List<Method> methods = et.getGenericType().getMethods();
    		List<Method> res = new ArrayList<Method>(methods.size());
    		for (Method m : methods) {
    			res.add(new ErasedMethod(m, this));
    		}
    		return res;
    	}
        if (ct instanceof CapturedTypeArgument) {
        	// TODO 0.90 !!!
        	TypeArgument ta = ((CapturedTypeArgument)ct).getTypeArgument();
        	if (ta.getWildcardMode() == WildcardMode.Any
        			|| ta.getWildcardMode() == WildcardMode.Super) {
        		// special handling required, but it's done in getSupertypes...
        		// None therefore...
        		return Collections.<Method>emptyList();
        	}
        	return getBaseType(ta).getMethods();
        }
    	assert ct == getNameInfo().getNullType();
        return null;
    }

    public List<Method> getAllMethods(ClassType ct) {
        if (ct instanceof IntersectionType 
    			|| ct instanceof ParameterizedType 
    			|| ct instanceof ArrayType
    			|| ct instanceof ErasedType
    			|| ct instanceof CapturedTypeArgument)
    		return super.getAllMethods(ct);
        return null;
    }

    public List<Constructor> getConstructors(ClassType ct) {
    	if (ct instanceof ParameterizedType) {
    		// TODO duplicate code...
    		ParameterizedType pt = (ParameterizedType)ct;
    		List<? extends Constructor> temp = pt.getGenericType().getConstructors();
    		List<Constructor> res = new ArrayList<Constructor>(temp.size());
    		for (Constructor m : temp) {
    			if (getServiceConfiguration().getSourceInfo().containsTypeParameter(m))
    				res.add(new ParameterizedConstructor(m, pt, this));
    			else 
    				res.add(m);
    		}
    		return res;
    	}
    	if (ct instanceof ErasedType) {
    		ErasedType et = (ErasedType)ct;
    		List<? extends Constructor> cons = et.getGenericType().getConstructors();
    		List<Constructor> res = new ArrayList<Constructor>(cons.size());
    		for (Constructor m : cons) {
    			res.add(new ErasedConstructor(m, this));
    		}
    		return res;
    	}
    	if (ct instanceof ArrayType) {
    		return Collections.<Constructor>emptyList();
    	}
    	if (ct instanceof CapturedTypeArgument) {
    		return null;
    	}
        // valid for NullType
    	assert ct == getNameInfo().getNullType();
        return null;
    }

    public ClassType getContainingClassType(Member m) {
        if (m instanceof DefaultConstructor || m instanceof ImplicitEnumMethod) {
            return m.getContainingClassType();
        }
        // TODO 0.90 valid for ...
        return null;
    }

    public List<Type> getSignature(Method m) {
    	if (m instanceof ImplicitEnumValueOf) {
    		ArrayList<Type> tal = new ArrayList<Type>(1);
        	tal.add(getServiceConfiguration().getNameInfo().getJavaLangString());
        	return tal;
    	} else if (m instanceof ParameterizedMethod) {
    		// TODO 0.90 - Cache?
    		ParameterizedMethod pm = (ParameterizedMethod)m;
    		return replaceAllTypeParametersWithArgs(pm.getGenericMethod().getSignature(), 
    				pm.getContainingClassType().getDefinedTypeParameters(), 
    				pm.getContainingClassType().getAllTypeArgs());
//    		
    	} else if (m instanceof ErasedMethod) {
    		// TODO 0.90 - Cache?
    		return eraseTypes(((ErasedMethod)m).getGenericMethod().getSignature());
    	} else if (m instanceof ResolvedGenericMethod) {
        	// TODO 0.90
    		ResolvedGenericMethod rgm = (ResolvedGenericMethod)m;
    		return replaceAllTypeParameters(rgm.getGenericMethod().getSignature(), 
    				rgm.getGenericMethod().getTypeParameters(), 
    				rgm.getReplacementType(), false);
        }

        // valid for DefaultConstructor, values() in enums, and ArrayCloneMethod
    	assert m instanceof DefaultConstructor || m instanceof ArrayCloneMethod || m instanceof ImplicitEnumValues;
        return Collections.<Type>emptyList();
    }

    private List<ClassType> enumValueOfExceptions = null;
    public List<ClassType> getExceptions(Method m) {
    	if (m instanceof ImplicitEnumValueOf) {
    		if (enumValueOfExceptions == null) {
    		    // since list is not visible as mutable, can cache result here.  
    			enumValueOfExceptions = new ArrayList<ClassType>(2);
    			enumValueOfExceptions.add(getNameInfo().getClassType("java.lang.IllegalArgumentException"));
    			enumValueOfExceptions.add(getNameInfo().getClassType("java.lang.NullPointerException"));
    			enumValueOfExceptions = Collections.unmodifiableList(enumValueOfExceptions);
    	    }
    		return enumValueOfExceptions;
    	} else if (m instanceof ParameterizedMethod) {
    		// TODO 0.90 - Cache ?
    		ParameterizedMethod pm = (ParameterizedMethod)m;
    		return replaceAllTypeParametersWithArgs(pm.getGenericMethod().getExceptions(), 
    				pm.getContainingClassType().getDefinedTypeParameters(), 
    				pm.getContainingClassType().getAllTypeArgs());
//    		return (List)replaceTypeArgs(pm.getGenericMethod().getExceptions(),
//    							   pm.getContainingClassType().getTypeArgs(),
//    							   pm.getContainingClassType().getGenericType().getTypeParameters());
    	} else if (m instanceof ErasedMethod) {
    		return eraseTypes(((ErasedMethod)m).getGenericMethod().getExceptions());
    	} else if (m instanceof ResolvedGenericMethod) {
        	// TODO 0.90
        	throw new RuntimeException();
        }
    	
        // valid for Default Constructor and values() in enums.
    	assert m instanceof DefaultConstructor || m instanceof ImplicitEnumValues;
        return new ArrayList<ClassType>(0);
    }
    
    public Type getReturnType(Method m) {
    	if (m instanceof ImplicitEnumValueOf) {
    		return m.getContainingClassType();
    	}  else if (m instanceof ImplicitEnumValues) {
    		return getServiceConfiguration().getNameInfo().createArrayType(m.getContainingClassType());
    	} else if (m instanceof ParameterizedMethod) {
    		// TODO 0.90 - cache ?
    		ParameterizedMethod pm = (ParameterizedMethod)m;
    		Type genRet = pm.getGenericMethod().getReturnType();
    		
    		return replaceAllTypeParametersWithArgs(genRet, 
    				pm.getContainingClassType().getDefinedTypeParameters(), 
    				pm.getContainingClassType().getAllTypeArgs(),
    				pm.getGenericMethod().getTypeParameters());
//    		
//    		if (genRet != null && genRet.getName().endsWith("T[]"))
//    			System.out.println();
//    		
//    		int dim = 0;
//    		Type baseGenRet = genRet;
//    		while (baseGenRet instanceof ArrayType) {
//    			baseGenRet = ((ArrayType)baseGenRet).getBaseType();
//    			dim++;
//    		}
//    		
//    		// TODO 0.90 does this belong here?
//    		// check method type arguments first...
//    		
//    		
//    		if (!(baseGenRet instanceof TypeParameter))
//    			return genRet; // that's the original type!
//    		Type res =  replaceTypeArg((ClassType)baseGenRet, 
//    							  pm.getContainingClassType().getTypeArgs(), 
//    							  pm.getContainingClassType().getGenericType().getTypeParameters());
//    		while (dim-- > 0) {
//    			res = res.createArrayType();
//    		}
//    		return res;
    	} else if (m instanceof ArrayCloneMethod) {
    		// JLS §10.7 (2nd / 3rd edition, respectively)
    		if (getServiceConfiguration().getProjectSettings().java5Allowed()) {
    			ArrayCloneMethod acm = (ArrayCloneMethod)m;
    			return acm.getContainingClassType();
    		}
    		else { 
    			return getServiceConfiguration().getNameInfo().getJavaLangObject();
    		}
    	} else if (m instanceof ErasedMethod) {
    		return eraseType(((ErasedMethod)m).getGenericMethod().getReturnType());
    	} else if (m instanceof ResolvedGenericMethod) {
    		ResolvedGenericMethod rgm = (ResolvedGenericMethod)m;
    		Type res = rgm.getGenericMethod().getReturnType();
    		if (res == null) {
    			// generic method, but void as return type. This is valid,
    			// e.g. java.util.Arrays.sort()
    			return null;
    		}
    		return replaceAllTypeParameters(res, rgm.getGenericMethod().getTypeParameters(),
    				rgm.getReplacementType(), true);
    	}
        // valid for Default Constructor
    	assert m instanceof DefaultConstructor;
        return null;
    }
}
