/*
 * Created on 31.03.2006
 *
 * This file is part of the RECODER library and protected by the LGPL.
 * 
 */
package recoder.kit.transformation.java5to4;

import java.util.ArrayList;
import java.util.Dictionary;
import java.util.Hashtable;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.abstraction.ArrayType;
import recoder.abstraction.ClassType;
import recoder.abstraction.Method;
import recoder.abstraction.ParameterizedType;
import recoder.abstraction.PrimitiveType;
import recoder.abstraction.Type;
import recoder.abstraction.TypeArgument;
import recoder.abstraction.TypeParameter;
import recoder.bytecode.TypeParameterInfo;
import recoder.convenience.TreeWalker;
import recoder.java.CompilationUnit;
import recoder.java.Expression;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.StatementContainer;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.TypeArgumentDeclaration;
import recoder.java.expression.ParenthesizedExpression;
import recoder.java.reference.MemberReference;
import recoder.java.reference.MethodReference;
import recoder.java.reference.ReferenceSuffix;
import recoder.java.reference.TypeReference;
import recoder.java.reference.VariableReference;
import recoder.kit.MethodKit;
import recoder.kit.MiscKit;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.kit.TypeKit;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/**
 * This transformation does not work yet!
 *
 *
 * uses type casts instead of co-variant return types.
 * Does not work with primitive types yet.
 * @author Tobias Gutzmann
 *
 */
public class RemoveCoVariantReturnTypes extends TwoPassTransformation {
	private NonTerminalProgramElement root;
	
	private static class IntroduceCast {
		Expression toBeCasted;
		TypeReference castedType;
		IntroduceCast(Expression e, TypeReference tr) {
			this.toBeCasted = e;
			this.castedType = tr;
		}
	}
	
	private static class ReturnTypeRefReplacement {
		TypeReference typeParamRef;
		TypeReference replacement;
		ReturnTypeRefReplacement(TypeReference from, TypeReference to) {
			this.typeParamRef = from;
			this.replacement = to;
//			if (from.getTypeArguments() != null)
//				to.setTypeArguments(from.getTypeArguments());
		}
	}
	
//	private List<Item> items;
//	private List<Item> parameterizedItems;
	private Dictionary<Method, Type> visitedMethods;
	private List<CompilationUnit> cul;
	private List<IntroduceCast> casts;
	private List<ReturnTypeRefReplacement> covariantReturnTypes;

	
	/**
	 * 
	 */
	public RemoveCoVariantReturnTypes(CrossReferenceServiceConfiguration sc, NonTerminalProgramElement root) {
		super(sc);
		this.root = root;
		cul = new ArrayList<CompilationUnit>();
		cul.add((CompilationUnit)root);
	}
	
	public RemoveCoVariantReturnTypes(CrossReferenceServiceConfiguration sc, List<CompilationUnit> cul) {
		super(sc);
		this.cul = cul;
		root = cul.get(0);
	}
	
	@Override
	public ProblemReport analyze() {
//		this.items = new ArrayList<Item>();
//		this.parameterizedItems = new ArrayList<Item>();
		this.visitedMethods = new Hashtable<Method, Type>();
		this.casts = new ArrayList<IntroduceCast>();
		this.covariantReturnTypes = new ArrayList<ReturnTypeRefReplacement>();
		for (CompilationUnit cu : cul) {
			root = cu;
			TreeWalker tw = new TreeWalker(root);
			while (tw.next()) {
				ProgramElement pe = tw.getProgramElement();
				if (pe instanceof MethodDeclaration) {
					MethodDeclaration md = (MethodDeclaration)pe;
					Type returnType = getSourceInfo().getReturnType(md);
					if (returnType == null || returnType instanceof PrimitiveType || visited(md) != null) {
						continue;
					}
					List<Method> ml = MethodKit.getRedefinedMethods(md);
					if (ml == null || ml.size() == 0) continue;
					Type originalType = getRedefinedMethodsRecursive(ml);
					if (md.getName().equals("getResolvedAnnotation")) {
						System.out.println("getResolvedAnnotation " + md.getFullName() + " " + originalType.getFullName() + " " + md.getReturnType().getFullName());
					}
					
					if (originalType != null && !(originalType.getFullName().equals(returnType.getFullName()))) {
						// covariant return type...
						if (!(originalType instanceof TypeParameter) && !(originalType instanceof TypeParameterInfo)) {
							createItem(md, returnType, originalType);
						}
					}
				}
				else if(pe instanceof VariableReference) {
					Type t = getSourceInfo().getType(pe);
					VariableReference vr = (VariableReference)pe;
					if (t instanceof ArrayType) {
						if (vr.getReferenceSuffix() != null) {
							ReferenceSuffix rs = vr.getReferenceSuffix();
							if (rs instanceof MethodReference) {
								MethodReference mr = (MethodReference)rs;
								if (mr.getName().equals("clone")) {
									casts.add(new IntroduceCast(mr, TypeKit.createTypeReference(getProgramFactory(), t)));
								}
							}
						}
						else if (vr.getASTParent() instanceof ParenthesizedExpression) {
							ParenthesizedExpression parEx = (ParenthesizedExpression)vr.getASTParent();
							if (parEx.getReferenceSuffix() != null) {
								ReferenceSuffix rs = parEx.getReferenceSuffix();
								if (rs instanceof MethodReference) {
									MethodReference mr = (MethodReference)rs;
									if (mr.getName().equals("clone")) {
										casts.add(new IntroduceCast(mr, TypeKit.createTypeReference(getProgramFactory(), t)));
									}
								}
							}
						}
					}
				} else if (pe instanceof MethodReference) {
					Type t = getSourceInfo().getType(pe);
					MethodReference mRef = (MethodReference)pe;
					if (t instanceof ArrayType) {
						if (mRef.getReferenceSuffix() != null) {
							ReferenceSuffix rs = mRef.getReferenceSuffix();
							if (rs instanceof MethodReference) {
								MethodReference mr = (MethodReference)rs;
								if (mr.getName().equals("clone")) {
									casts.add(new IntroduceCast(mr, TypeKit.createTypeReference(getProgramFactory(), t)));
								}
							}
						}
						else if (mRef.getASTParent() instanceof ParenthesizedExpression) {
							ParenthesizedExpression parEx = (ParenthesizedExpression)mRef.getASTParent();
							if (parEx.getReferenceSuffix() != null) {
								ReferenceSuffix rs = parEx.getReferenceSuffix();
								if (rs instanceof MethodReference) {
									MethodReference mr = (MethodReference) rs;
									if (mr.getName().equals("clone")) {
										casts.add(new IntroduceCast(mr, TypeKit.createTypeReference(getProgramFactory(), t)));
									}
								}
							}
						}
					}
				}
			}
		}
		return super.analyze();
	}
	
	private Type visited(Method md) {
		Type t = null;
		t = visitedMethods.get(md);
//		if (t != null) System.out.println("visited was true");
		return t;
	}	

	private void createItem(MethodDeclaration md, Type returnType, Type originalType) {
		visitedMethods.put(md, originalType);
//		System.out.println(returnType.getFullName() + " " + originalType.getFullName() + " " + md.getFullName());
//		System.out.println("Method: " + md.getName() + " in Class " + md.getContainingClassType().getName());
		ProgramFactory f = getProgramFactory();
		List<MemberReference> references = getCrossReferenceSourceInfo().getReferences(md);
		TypeReference newReturnTypeReference = TypeKit.createTypeReference(f, originalType, true);
		TypeReference oldReturnTypeReference = TypeKit.createTypeReference(f, returnType, true);
		oldReturnTypeReference.setParent(md);
		ASTList<TypeArgumentDeclaration> tadl = new ASTArrayList<TypeArgumentDeclaration>();
		try {
			TypeReference tmpRef = f.parseTypeReference(originalType.getFullName());
			if (newReturnTypeReference.getTypeArguments() != null )
				tmpRef.setTypeArguments(newReturnTypeReference.getTypeArguments().deepClone());
			newReturnTypeReference = tmpRef.deepClone();
			if (oldReturnTypeReference.getTypeArguments() != null && originalType instanceof ParameterizedType) {
				ParameterizedType pt = (ParameterizedType)originalType;
				for (TypeArgument ta : pt.getTypeArgs()) {
					try {
						if (ta instanceof TypeArgumentDeclaration && !(getSourceInfo().getType(((TypeArgumentDeclaration)ta).getTypeReference().getName(),md) instanceof TypeParameter)) {
							Type type = getSourceInfo().getType(((TypeArgumentDeclaration)ta).getTypeReference());
							tadl.add(new TypeArgumentDeclaration(f.parseTypeReference(type.getFullName()),ta.getWildcardMode()));
						}
					}
					catch (ParserException ex) {
						System.out.println("Parsing Exception");
					}
				}
				if (tadl.size() > 0)  {
					newReturnTypeReference.setTypeArguments(tadl.deepClone());
					newReturnTypeReference.makeAllParentRolesValid();
				}
			}
		}
		catch (ParserException ex) {
			System.err.println("Parsing Exception");
		}
		covariantReturnTypes.add(new ReturnTypeRefReplacement(md.getTypeReference(), newReturnTypeReference.deepClone()));
		
		boolean containsTypeParam = false;
		if (newReturnTypeReference.getTypeArguments() != null) {
			for (TypeArgumentDeclaration tad : newReturnTypeReference.getTypeArguments()) {
				if (getSourceInfo().getType(tad.getTypeReference().getName(),md) instanceof TypeParameter) {
					containsTypeParam = true;
				}
			}
		}
		
		for (MemberReference memRef : references) {
			MethodReference mr = (MethodReference)memRef;
			TypeReference castTo = oldReturnTypeReference.deepClone();
			if (castTo.getTypeArguments() != null) {
				if (!containsTypeParam) {
					List<TypeArgumentDeclaration> listOld = oldReturnTypeReference.getTypeArguments();
					List<TypeArgumentDeclaration> listNew = castTo.getTypeArguments();
					for (int i = 0; i < castTo.getTypeArguments().size(); i++) {
						try {
							Type t = getSourceInfo().getType(listOld.get(i).getTypeReference().getName(),mr);
							String fullName;
							if (t != null) {
								fullName = t.getFullName();
							}
							else {
								fullName = listOld.get(i).getTypeReference().getName();
							}
							
							listNew.get(i).setTypeReference(f.parseTypeReference(fullName));
						}
						catch(ParserException e) {
							System.out.println("Parsing Exception I");
						}
					}
					castTo.makeAllParentRolesValid();
					casts.add(new IntroduceCast(mr, castTo));
				}
				else {
					Type tmp = getSourceInfo().getType(mr);
					castTo = TypeKit.createTypeReference(f, tmp, true);
					ParameterizedType pt = (ParameterizedType)tmp;
					if (castTo.getTypeArguments() != null && pt.getTypeArgs().size() == castTo.getTypeArguments().size()) {
						for (int i = 0; i < castTo.getTypeArguments().size(); i++) {
							try {
								TypeArgumentDeclaration tad = castTo.getTypeArguments().get(i);
								tad.setTypeReference(f.parseTypeReference(pt.getTypeArgs().get(i).getTypeName()));
							}
							catch(Exception e) {
								System.out.println("Parsing Exception II");
							}
						}
					}
					castTo.makeAllParentRolesValid();
					casts.add(new IntroduceCast(mr, castTo));
				}
			}
			else {
				oldReturnTypeReference.makeAllParentRolesValid();
//				casts.add(new IntroduceCast(mr, oldReturnTypeReference));
				try {
					casts.add(new IntroduceCast(mr, f.parseTypeReference(md.getReturnType().getFullName())));				
				}
				catch(Exception e) {
					System.out.println("Parsing Exception II");
				}
			}
		}
	}
	
	private Type getRedefinedMethodsRecursive(List<Method> ml) {
		Type originalType = null;
		List<Method> tmp = new ArrayList<Method>();

		if (ml.size() > 1) {
			// inherited from different interfaces
			// get return types
			List<Type> returnTypes = new ArrayList<Type>();
			for(Method m : ml) {
				if (visited(m) == null) {
					tmp = MethodKit.getRedefinedMethods(m);
					if (tmp.size() == 0 && !(getSourceInfo().getReturnType(m) instanceof TypeParameter)) returnTypes.add(getSourceInfo().getReturnType(m));
					else returnTypes.add(getRedefinedMethodsRecursive(tmp));
				}
				else returnTypes.add(visitedMethods.get(m));
			}
			// get common supertype
			originalType = returnTypes.get(0);
			for (int i = 1; i < returnTypes.size(); i++) {
				if (!(originalType.getFullName().equals(returnTypes.get(i).getFullName())))
					originalType = getSourceInfo().getCommonSupertype((ClassType)originalType, (ClassType)returnTypes.get(i));
			}
			// some of the overwritten methods with covariant returnTypes themselves??
			for(int i = 0; i < ml.size(); i++) {
				Type returnType = returnTypes.get(i);
				if (originalType != null && returnType != null && !(originalType.getFullName().equals(returnType.getFullName())) &&
						ml.get(i) instanceof MethodDeclaration && visited(ml.get(i)) == null) {
						MethodDeclaration md = (MethodDeclaration)ml.get(i);
						createItem(md, returnType, originalType);
						List<Method> subMethL = MethodKit.getRedefiningMethods(getCrossReferenceSourceInfo(), md);
						for (Method subM : subMethL) {
							if (subM instanceof MethodDeclaration) {
								MethodDeclaration subMD = (MethodDeclaration)subM;
								if (visited(subMD) == null) createItem(subMD, subMD.getReturnType(), originalType);
								else if (!visited(subMD).equals(originalType)) createItem(subMD, visited(subMD), originalType);
							}
						}
				}
			}
		}
		else {
			if (ml.get(0) instanceof MethodDeclaration) {
				MethodDeclaration md = (MethodDeclaration)ml.get(0);
				tmp = MethodKit.getRedefinedMethods(md);
				if (tmp.size() == 0) {
					//end of recursion
					if (!(getSourceInfo().getReturnType(md) instanceof TypeParameter))
							originalType = getSourceInfo().getReturnType(md);
				}
				else {
					originalType = getRedefinedMethodsRecursive(tmp);
					Type returnType = getSourceInfo().getReturnType(md);
					if (visited(md) == null && returnType != null && originalType != null && !(returnType.getFullName().equals(originalType.getFullName()))) {
						createItem(md, returnType, originalType);
						List<Method> subMethL = MethodKit.getRedefiningMethods(getCrossReferenceSourceInfo(), md);
						for (Method subM : subMethL) {
							if (subM instanceof MethodDeclaration) {
								MethodDeclaration subMD = (MethodDeclaration)subM;
								if (visited(subMD) == null) createItem(subMD, subMD.getReturnType(), originalType);
								else if (!visited(subMD).equals(originalType)) createItem(subMD, visited(subMD), originalType);
							}
						}
					}
				}
			}
			else {
				if (!(ml.get(0).getReturnType() instanceof TypeParameter))
				originalType = ml.get(0).getReturnType();
			}
		}
		return originalType;
	}
	
	private boolean isChild(NonTerminalProgramElement ex1, Expression ex2) {
		Expression tmp;
		boolean result = false;
		for (int c = 0; c < ex1.getChildCount(); c++) {
			if (ex1.getChildAt(c) instanceof Expression) {
				tmp = (Expression)ex1.getChildAt(c);
				if (tmp.equals(ex2)) return true;
				else if (ex1.getChildAt(c) instanceof NonTerminalProgramElement) {
					result = isChild((NonTerminalProgramElement) ex1.getChildAt(c), ex2);
					if (result) return true;
				}
			}
			else if(ex1.getChildAt(c) instanceof NonTerminalProgramElement) {
				result = isChild((NonTerminalProgramElement)ex1.getChildAt(c),ex2);
				if (result) return true;
			}
		}
		return result;
	}
	
	private void sortCasts(List<IntroduceCast> casts) {
		boolean changed = true;
		Expression ex1, ex2;
		IntroduceCast tmp;
		NonTerminalProgramElement ntpe = null;
		while(changed) {
			changed = false;
			for (int i = 0; i < casts.size() - 1; i++) {
				for (int j = i + 1; j < casts.size(); j++) {
					ex1 = casts.get(i).toBeCasted;
					ex2 = casts.get(j).toBeCasted;
					if (ex1 instanceof NonTerminalProgramElement) {
						ntpe = (NonTerminalProgramElement) ex1;
						if (isChild(ntpe, ex2)) {
							tmp = casts.get(i);
							casts.set(i, casts.get(j));
							casts.set(j, tmp);
							changed = true;
						}
					}
				}
			}
		}
	}
	
	@Override
	public void transform() {
		super.transform();
		System.out.println("casts: " + casts.size() + " covariantReturnTypes: " + covariantReturnTypes.size());
		ProgramFactory f = getProgramFactory();
		for (ReturnTypeRefReplacement rtrr : covariantReturnTypes) {
			if (rtrr.typeParamRef.getASTParent().getIndexOfChild(rtrr.typeParamRef) != -1)
				replace(rtrr.typeParamRef, rtrr.replacement);
		}
		sortCasts(casts);
		for (IntroduceCast c : casts) {
			MiscKit.unindent(c.toBeCasted);
			if (c.toBeCasted.getASTParent().getIndexOfChild(c.toBeCasted) != -1 
				&&	!(c.toBeCasted.getASTParent() instanceof StatementContainer))
					replace(c.toBeCasted, f.createParenthesizedExpression(f.createTypeCast(c.toBeCasted.deepClone(), c.castedType)));
		}
	}
}
