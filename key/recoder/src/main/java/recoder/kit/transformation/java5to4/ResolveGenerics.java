/*
 * Created on 01.04.2006
 *
 * This file is part of the RECODER library and protected by the LGPL.
 * 
 */
package recoder.kit.transformation.java5to4;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.abstraction.ArrayType;
import recoder.abstraction.ClassType;
import recoder.abstraction.ErasedMethod;
import recoder.abstraction.Method;
import recoder.abstraction.ParameterizedMethod;
import recoder.abstraction.ParameterizedType;
import recoder.abstraction.PrimitiveType;
import recoder.abstraction.Type;
import recoder.abstraction.TypeParameter;
import recoder.abstraction.Variable;
import recoder.abstraction.TypeArgument.CapturedTypeArgument;
import recoder.abstraction.TypeArgument.WildcardMode;
import recoder.bytecode.ClassFile;
import recoder.bytecode.MethodInfo;
import recoder.bytecode.TypeParameterInfo;
import recoder.convenience.TreeWalker;
import recoder.java.Comment;
import recoder.java.CompilationUnit;
import recoder.java.Expression;
import recoder.java.Import;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.StatementContainer;
import recoder.java.declaration.InheritanceSpecification;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.TypeArgumentDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.TypeParameterDeclaration;
import recoder.java.declaration.VariableDeclaration;
import recoder.java.declaration.VariableSpecification;
import recoder.java.expression.Assignment;
import recoder.java.expression.ParenthesizedExpression;
import recoder.java.expression.operator.New;
import recoder.java.expression.operator.NewArray;
import recoder.java.expression.operator.TypeCast;
import recoder.java.reference.FieldReference;
import recoder.java.reference.MemberReference;
import recoder.java.reference.MethodReference;
import recoder.java.reference.ReferenceSuffix;
import recoder.java.reference.TypeReference;
import recoder.java.reference.VariableReference;
import recoder.java.statement.EnhancedFor;
import recoder.java.statement.Return;
import recoder.kit.MethodKit;
import recoder.kit.MiscKit;
import recoder.kit.ProblemReport;
import recoder.kit.TransformationNotApplicable;
import recoder.kit.TwoPassTransformation;
import recoder.kit.TypeKit;
import recoder.kit.UnitKit;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.CrossReferenceSourceInfo;
import recoder.service.SourceInfo;

public class ResolveGenerics extends TwoPassTransformation {
	
	private void resolveTypeParameters(
			List<TypeParameterDeclaration> typeParams
	) {
		// deal with type parameter uses in own Type Declaration first
//		System.out.println("ResolveGenerics: analyze with all the parameters");
		
		Arrays.asList(new Object[][] {
                { "0s", 35
        },
                { "25s", (25 * 1000)
        },
                { "5m 0s", (60 * 1000 * 5)
        },
                { "2h 0m 0s", (60 * 1000 * 120)
        } });
		
		CrossReferenceSourceInfo ci = getCrossReferenceSourceInfo();
		for (int i = 0, s = typeParams.size(); i < s; i++) {
			TypeParameterDeclaration tpd = typeParams.get(i);
			TypeReference repl;
			ClassType resolvedType;
			if (tpd.getBounds() == null || tpd.getBounds().size() == 0) {
				resolvedType = ci.getServiceConfiguration().getNameInfo().getJavaLangObject();
				repl = TypeKit.createTypeReference(ci, resolvedType, tpd); // in rare cases where another type named "Object" is used (e.g. Corba applications)
			} else {
				resolvedType = (ClassType)ci.getType(tpd.getBounds().get(0));
//				System.out.println("Bound: " + resolvedType.getFullName() + " " + tpd.getBounds().size());
				repl = makeReplacement(tpd);
//				System.out.println(repl.getName());
			}
			Type rt = tpd;
//			int dim = 0;
			do {
				List<TypeReference> tprl = ci.getReferences(rt);
				for (int j = 0, t = tprl.size(); j < t; j++) {
					TypeReference tr = tprl.get(j);
					if (!(tr.getASTParent() instanceof TypeArgumentDeclaration))
						typeParamReferences.add(new TypeParamRefReplacement(tr, repl.deepClone()));
					else stuffToBeRemoved.add(tr.getASTParent());
				}
				rt = ci.getServiceConfiguration().getNameInfo().getArrayType(rt);
//				if (rt != null) System.out.println(rt.getFullName());
//				dim++;
				repl.setDimensions(repl.getDimensions()+1);
			}  while (rt != null); 
		}
	}
	
	
	
	private TypeReference makeReplacement(TypeParameterDeclaration tpd) {
//		System.out.println("ResolveGenerics: makeReplacement");
		ProgramFactory f = getProgramFactory();
		CrossReferenceSourceInfo ci = getCrossReferenceSourceInfo();
		TypeReference repl;
		TypeReference tr;
		List<Method> meth = null;
		List<MemberReference> methRefs = null;
		repl = tpd.getBounds().get(0).deepClone();
		if (tpd.getBoundCount() > 1) {
			StringBuffer text = new StringBuffer("/*");
			for (int x = 1; x < tpd.getBoundCount(); x++) {
				tr = tpd.getBounds().get(x);
				ClassType ct = (ClassType)ci.getType(tr);
				meth = ct instanceof ParameterizedType ? ((ParameterizedType)ct).getAllMethods() : ci.getMethods(ci.getTypeDeclaration(ct));
				for (Method m : meth) {
					methRefs = ci.getReferences(m);
					for (MemberReference mr : methRefs) {
						if (UnitKit.getCompilationUnit(tpd) == UnitKit.getCompilationUnit(mr)) {
//							System.out.println(((MethodReference)mr).getName());
							if (((MethodReference)mr).getReferencePrefix() instanceof Expression)
								casts.add(new IntroduceCast((Expression)((MethodReference)mr).getReferencePrefix(), tr));
						}
					}
				}
				text.append(" & ");
				text.append(tpd.getBoundName(x));
			}
			text.append(" */");
			repl.setComments(new ASTArrayList<Comment>(f.createComment(text.toString(), false)));
		}
		return repl;
	}

	private static class IntroduceCast {
		Expression toBeCasted;
		TypeReference castedType;
		IntroduceCast(Expression e, TypeReference tr) {
			this.toBeCasted = e;
			this.castedType = tr;
		}
	}

	private static class TypeParamRefReplacement {
		TypeReference typeParamRef;
		TypeReference replacement;
		TypeParamRefReplacement(TypeReference from, TypeReference to) {
			this.typeParamRef = from;
			this.replacement = to;
			replacement.setTypeArguments(null);
		}
	}
	
//	private class IntroduceBoxing {
//		Expression toBeCasted;
//		MethodReference replacement;
//		IntroduceBoxing(Expression e1, PrimitiveType t) {
//			this.toBeCasted = e1;
//			NameInfo ni = getServiceConfiguration().getNameInfo();
//			ProgramFactory f = getProgramFactory();
//			Identifier id;
//			TypeCast cast = null;
////			PrimitiveType t = toBox2.get(e);
//			if (t == ni.getBooleanType()) {
//				id = f.createIdentifier("booleanValue");
//				cast = new TypeCast(e1.deepClone(), TypeKit.createTypeReference(f, ni.getJavaLangBoolean()));
//			} else if (t == ni.getByteType()) {
//				id = f.createIdentifier("byteValue");
//				cast = new TypeCast(e1.deepClone(), TypeKit.createTypeReference(f, ni.getJavaLangByte()));
//			} else if (t == ni.getShortType()) {
//				id = f.createIdentifier("shortValue");
//				cast = new TypeCast(e1.deepClone(), TypeKit.createTypeReference(f, ni.getJavaLangShort()));
//			} else if (t == ni.getCharType()) {
//				id = f.createIdentifier("charValue");
//				cast = new TypeCast(e1.deepClone(), TypeKit.createTypeReference(f, ni.getJavaLangCharacter()));
//			} else if (t == ni.getIntType()) {
//				id = f.createIdentifier("intValue");
//				cast = new TypeCast(e1.deepClone(), TypeKit.createTypeReference(f, ni.getJavaLangInteger()));
//			} else if (t == ni.getLongType()) {
//				id = f.createIdentifier("longValue");
//				cast = new TypeCast(e1.deepClone(), TypeKit.createTypeReference(f, ni.getJavaLangLong()));
//			} else if (t == ni.getFloatType()) {
//				id = f.createIdentifier("floatValue");
//				cast = new TypeCast(e1.deepClone(), TypeKit.createTypeReference(f, ni.getJavaLangFloat()));
//			} else if (t == ni.getDoubleType()) {
//				id = f.createIdentifier("doubleValue");
//				cast = new TypeCast(e1.deepClone(), TypeKit.createTypeReference(f, ni.getJavaLangDouble()));
//			} else {
//				System.out.println("cannot box: " + t);
//				throw new Error();
//			}
//			replacement = f.createMethodReference(f.createParenthesizedExpression(cast), id);
//		}
//	}
	
	private List<CompilationUnit> cul;
//	private List<TwoPassTransformation> parts;
	private List<ProgramElement> stuffToBeRemoved;
//	private List<TwoPassTransformation> trParts;
	private List<IntroduceCast> casts;
	private List<TypeParamRefReplacement> typeParamReferences;
	private List<TypeParamRefReplacement> paramReplacements;
//	private List<IntroduceBoxing> boxingCasts;
	/**
	 * @param sc
	 */
	public ResolveGenerics(CrossReferenceServiceConfiguration sc, CompilationUnit cu) {
		super(sc);
		cul = new ArrayList<CompilationUnit>();
		cul.add(cu);
	}
	
	public ResolveGenerics(CrossReferenceServiceConfiguration sc, List<CompilationUnit> cul) {
		super(sc);
		this.cul = cul;
	}
	
//	public void addResolveSingleVariableDeclaration(CrossReferenceServiceConfiguration sc, VariableDeclaration vd) {
////		System.out.println("addResolveSingleVaraibleDeclaration");
//		TwoPassTransformation tpf = new ResolveSingleVariableDeclaration(sc, vd, this);
//		if (tpf.analyze() != IDENTITY)
//			trParts.add(tpf);
//	}
//	
//	public void addResolveMethodReturnType(CrossReferenceServiceConfiguration sc, MethodDeclaration md) {
//		TwoPassTransformation tpf = new ResolveMethodReturnType(sc, md, this);
//		if (tpf.analyze() != IDENTITY)
//			trParts.add(tpf);
//	}
	
//	public void addCasts(List<IntroduceCast> casts) {
//		this.casts.addAll(casts);
//	}
	
	private boolean isChild(NonTerminalProgramElement ex1, Expression ex2) {
		if (ex1 == ex2) return false;
		return MiscKit.contains(ex1, ex2);
	}
	
	private void sortCastsLoc(List<IntroduceCast> casts) {
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
	
	private void sortCasts(List<IntroduceCast> casts) {
		HashMap<ProgramElement, ArrayList<IntroduceCast>> temp = new HashMap<ProgramElement, ArrayList<IntroduceCast>>(casts.size());
		for (IntroduceCast cast : casts) {
			CompilationUnit decl = UnitKit.getCompilationUnit(cast.toBeCasted);
			ArrayList<IntroduceCast> al = temp.get(decl);
			if (al == null) {
				al = new ArrayList<IntroduceCast>(4);
				temp.put(decl, al);
			}
			al.add(cast);
		}
		casts.clear();
		for (ArrayList<IntroduceCast> al : temp.values()) {
			sortCastsLoc(al);
			casts.addAll(al);
		}
	}
	
	private boolean isLeftHandSide(ProgramElement pe) {
		ProgramElement parent = pe.getASTParent(), tmp = null;
		boolean res = false;
		while (parent != null) {
			if (parent instanceof Assignment && ((Assignment)parent).getExpressionAt(0).equals(pe) && ((Assignment)parent).getArity() == 2)
				return true;
			tmp = parent;
			parent = parent.getASTParent();
			pe = tmp;
		}
		return res;
	}
	
	private void resolveGenericMethod(MethodDeclaration md) {
		List<TypeParameterDeclaration> typeParams = md.getTypeParameters();
		if (typeParams == null || typeParams.size() == 0)
			return ;

//		System.out.println("ResolveGenericMethod: analyze()");
//		ProgramFactory f = getProgramFactory();
		
//		List<TypeParamRefReplacement> typeParamReferences = new ArrayList<TypeParamRefReplacement>();
		
		CrossReferenceSourceInfo ci = getCrossReferenceSourceInfo();
		resolveTypeParameters(typeParams);
		
		// now deal with type references using type arguments (no need to deal with raw types)
		List<MemberReference> mrl = ci.getReferences(md);
		for (int i = 0, s = mrl.size(); i < s; i++) {
			MethodReference mr = (MethodReference)mrl.get(i);
			List<TypeArgumentDeclaration> typeArgs = mr.getTypeArguments();
			if (typeArgs == null || typeArgs.size() == 0)
				continue;
			stuffToBeRemoved.addAll(typeArgs);
		}
		// remove type parameters
		stuffToBeRemoved.addAll(typeParams);
	}
	
	private void resolveMethodReturnType(Method md) {
		TypeReference tr = null;
		if (md instanceof MethodDeclaration)
			tr = ((MethodDeclaration)md).getTypeReference();
		Type returnType = md.getReturnType();
		
		if (!(returnType instanceof ParameterizedType) && !(returnType instanceof TypeParameter) && !(returnType instanceof ArrayType) && !(md instanceof ParameterizedMethod)) {
			return ;
		}
//		if (returnType instanceof TypeParameter && !(md instanceof MethodInfo)) return;
//		System.out.println("ResolveMethodReturnType: analyze() -- " + md.getFullName());
		CrossReferenceSourceInfo ci = getCrossReferenceSourceInfo();
		
		if (md instanceof MethodDeclaration) {
			if (tr != null && tr.getTypeArguments() != null)
				stuffToBeRemoved.addAll(tr.getTypeArguments());
		}
		
		List<MemberReference> mrl = ci.getReferences(md);
		for (int j = 0, t = mrl.size(); j < t; j++) {
			MethodReference vr = (MethodReference)mrl.get(j);
			returnType = md.getReturnType();

			NonTerminalProgramElement parent = vr.getASTParent();
			while (parent instanceof ParenthesizedExpression || parent instanceof TypeCast) {
				parent = parent.getASTParent();
			}
			
			Type ty = null;
			boolean argument = false;
			boolean firstTime = false;
			if (parent instanceof MethodReference || returnType instanceof TypeParameter || md instanceof ParameterizedMethod) {
				if ( (returnType instanceof TypeParameter || md instanceof ParameterizedMethod) || (((MethodReference)parent).getArguments() != null && ((MethodReference)parent).getArguments().contains(vr))) {
					ty = ci.getType(vr);
					if (ty != null && !(ty instanceof TypeParameter) && !(ty instanceof ArrayType)) {
//						if (returnType instanceof TypeParameter) System.out.println(vr.getName() + " " + ty.getFullName() + " " + ty.getClass());
						if (ty instanceof CapturedTypeArgument) {
							casts.add(new IntroduceCast(vr, resolveCapturedTypeArgument(ty)));
						}
						else casts.add(new IntroduceCast(vr, TypeKit.createTypeReference(ci, ty, parent)));
					}
					else if (parent instanceof Assignment) {
						ty = ci.getType(((Assignment)parent).getExpressionAt(0));
//						if (md.getName().equals("createFact")) System.out.println("createFact " + ty.getFullName() + " " + ty.getClass());
						if (!(ty instanceof TypeParameter)) {
							if (ty instanceof CapturedTypeArgument) {
								casts.add(new IntroduceCast(vr, resolveCapturedTypeArgument(ty)));
							}
							else {
								casts.add(new IntroduceCast(vr, TypeKit.createTypeReference(getProgramFactory(), ty.getFullName())));
							}
						}
						if (ty instanceof TypeParameter && ((TypeParameter)ty).getBoundCount() == 0) {
							casts.add(new IntroduceCast(vr, TypeKit.createTypeReference(getProgramFactory(), "Object")));
						}
						if (ty instanceof TypeParameter && ((TypeParameter)ty).getBoundCount() > 0) {
							TypeReference tmp =  TypeKit.createTypeReference(getProgramFactory(), ((TypeParameter)ty).getBoundName(0));
							if (md instanceof MethodDeclaration) tmp.setParent((MethodDeclaration)md);
							else tmp.setParent(vr);
							casts.add(new IntroduceCast(vr, TypeKit.createTypeReference(getProgramFactory(), ci.getType(tmp).getFullName())));
//							System.out.println("Cast zu " + tmp.getName());
						}
					}
					else if (parent instanceof Return) {
						NonTerminalProgramElement ntpe = parent;
						while (!(ntpe instanceof MethodDeclaration)) ntpe = ntpe.getASTParent();
						ty = ((MethodDeclaration)ntpe).getReturnType();
						if (!(ty instanceof TypeParameter)) {
							if (ty instanceof CapturedTypeArgument) {
								casts.add(new IntroduceCast(vr, resolveCapturedTypeArgument(ty)));
							}
							else {
								casts.add(new IntroduceCast(vr, TypeKit.createTypeReference(getProgramFactory(), ty.getFullName())));
							}
						}
						if (ty instanceof TypeParameter && ((TypeParameter)ty).getBoundCount() == 0) {
							casts.add(new IntroduceCast(vr, TypeKit.createTypeReference(getProgramFactory(), "Object")));
						}
						if (ty instanceof TypeParameter && ((TypeParameter)ty).getBoundCount() > 0) {
							TypeReference tmp =  TypeKit.createTypeReference(getProgramFactory(), ((TypeParameter)ty).getBoundName(0));
							if (md instanceof MethodDeclaration) tmp.setParent((MethodDeclaration)md);
							else tmp.setParent(vr);
							casts.add(new IntroduceCast(vr, TypeKit.createTypeReference(getProgramFactory(), ci.getType(tmp).getFullName())));
//							System.out.println("Cast zu II " + tmp.getName());
						}
					}
//					if (parent instanceof MethodReference) {
//						vr = (MethodReference)parent;
//						returnType = ci.getMethod(vr).getReturnType();
//						parent = parent.getASTParent();
//					}
					firstTime = true;
				}
			}
			
			while (parent instanceof MethodReference) {
				Expression toCast = null;
				// Argument
				if (((MethodReference)parent).getArguments() != null && ((MethodReference)parent).getArguments().contains(vr) && !firstTime) {
					ty = ci.getType(vr);
					toCast = vr;
					argument = true;
					firstTime = false;
				}
				// ReferenceSuffix
				else {
//					ty = ci.getContainingClassType(ci.getMethod((MethodReference)parent));
					ty = ci.getType(parent);
					toCast = (MethodReference)parent;
				}
				if (!(ty instanceof ClassType))
					break;
				if (!(ty instanceof TypeParameter)) {
					if (ty instanceof CapturedTypeArgument) {
						casts.add(new IntroduceCast(toCast, resolveCapturedTypeArgument(ty)));
					}
					else casts.add(new IntroduceCast(toCast, TypeKit.createTypeReference(ci, ty, parent)));
				}
				if (ty instanceof TypeParameter) {
					if ((ty instanceof TypeParameterDeclaration && ((TypeParameterDeclaration)ty).getBoundCount() == 1) || (ty instanceof TypeParameterInfo && ((TypeParameterInfo)ty).getBoundCount() == 1)) {
						if (ty instanceof CapturedTypeArgument) {
							casts.add(new IntroduceCast(toCast, resolveCapturedTypeArgument(ty)));
						}
						else {
							if (ty instanceof TypeParameterDeclaration)
								casts.add(new IntroduceCast(toCast, TypeKit.createTypeReference(ci, ci.getType(((TypeParameterDeclaration)ty).getBounds().get(0)), vr)));
							else
								casts.add(new IntroduceCast(toCast, TypeKit.createTypeReference(getProgramFactory(), ((TypeParameterInfo)ty).getBoundName(0))));
						}
					}
					else if ((ty instanceof TypeParameterDeclaration && ((TypeParameterDeclaration)ty).getBoundCount() == 0) || (ty instanceof TypeParameterInfo && ((TypeParameterInfo)ty).getBoundCount() == 0)) {
						casts.add(new IntroduceCast(toCast, TypeKit.createTypeReference(getProgramFactory(), "Object")));
					}
					else if ((ty instanceof TypeParameterDeclaration && ((TypeParameterDeclaration)ty).getBoundCount() > 0) || (ty instanceof TypeParameterInfo && ((TypeParameterInfo)ty).getBoundCount() > 0)) {
						System.out.println("More than one bound " + ty.getName() + " " + vr.toSource());
					}
				}
//				if(ty instanceof TypeParameter && returnType instanceof ParameterizedType) {
//					ParameterizedType pt = (ParameterizedType)returnType;
//					System.out.println(toCast.toSource() + " " + ty.getFullName() + " " + returnType.getFullName() + " " + md.getFullName());
//					if (pt.getTypeArgs().get(0) instanceof TypeArgumentDeclaration) {
//						Type tmp = ci.getType((TypeArgumentDeclaration)pt.getTypeArgs().get(0));
////						System.out.println("ResolveMethodReturnType: analyze -> " + ((MethodReference)parent).getName() + " " + tmp.getFullName());
//						if (tmp instanceof CapturedTypeArgument) {
//							casts.add(new IntroduceCast(toCast, resolveCapturedTypeArgument(tmp)));
//						}
//						else casts.add(new IntroduceCast(toCast, TypeKit.createTypeReference(ci, tmp, parent)));
//					}
//				}
				if (argument) break;
				vr = (MethodReference)parent;
				returnType = ci.getMethod(vr).getReturnType();
				parent = parent.getASTParent();
				while (parent instanceof ParenthesizedExpression || parent instanceof TypeCast) {
					parent = parent.getASTParent();
				}
			} 
		}
	}
	
	private void resolveSingleGenericType(TypeDeclaration td) {
		List<TypeParameterDeclaration> typeParams = td.getTypeParameters();
		if (typeParams == null || typeParams.size() == 0)
			return ;
		
//		System.out.println("ResolveSingleGenericType: analyze()");
//		List<TypeParamRefReplacement> typeParamReferences = new ArrayList<TypeParamRefReplacement>();

		CrossReferenceSourceInfo ci = getCrossReferenceSourceInfo();

		resolveTypeParameters(typeParams);
		
		// now deal with type references using type arguments (no need to deal with raw types)
		List<TypeReference> trl = ci.getReferences(td);
		for (int i = 0, s = trl.size(); i < s; i++) {
			TypeReference tr = trl.get(i);
			if (tr.getASTParent() instanceof VariableDeclaration) {
				if (UnitKit.getCompilationUnit(td).equals(UnitKit.getCompilationUnit(tr.getASTParent())))
					resolveSingleVariableDeclaration((VariableDeclaration)tr.getASTParent());
			}
			if (tr.getASTParent() instanceof MethodDeclaration) {
				if (UnitKit.getCompilationUnit(td).equals(UnitKit.getCompilationUnit(tr.getASTParent())))
					resolveMethodReturnType((MethodDeclaration)tr.getASTParent());
			}
			List<TypeArgumentDeclaration> typeArgs = tr.getTypeArguments();
			if (typeArgs == null || typeArgs.size() == 0)
				continue;
			stuffToBeRemoved.addAll(typeArgs);
		}
		// remove type parameters
		stuffToBeRemoved.addAll(typeParams);
	}
	
	private void resolveSingleVariableDeclaration(VariableDeclaration vd) {
		TypeReference tr = vd.getTypeReference();
		CrossReferenceSourceInfo ci = getCrossReferenceSourceInfo();
		Type returnType = ci.getType(tr);
		if ((tr.getTypeArguments() == null || tr.getTypeArguments().size() == 0) && !(returnType instanceof TypeParameter)) {
			return ;
		}
//		System.out.println("ResolveSingleVariableDeclaration: analyze()");
		

		
		if (tr.getTypeArguments() != null && tr.getTypeArguments().size() > 0) stuffToBeRemoved.addAll(tr.getTypeArguments());
		
		for (int i = 0, s = vd.getVariables().size(); i < s; i++) {
			VariableSpecification vs = vd.getVariables().get(i);
//			if (vs.getName().equals("l")) System.out.println("l");
			List<? extends VariableReference> vrl = ci.getReferences(vs);
			for (int j = 0, t = vrl.size(); j < t; j++) {
				VariableReference vr = vrl.get(j);
				if (isLeftHandSide(vr)) continue;
				ReferenceSuffix parent = vr.getReferenceSuffix();
				Type tmp = ci.getType(vr);
				if (returnType instanceof TypeParameter) {
					if (tmp != null && !(tmp instanceof TypeParameter) && !(tmp instanceof ArrayType)) {
//						System.out.println(vs.getFullName() + " " + tmp.getFullName() + " " + tmp.getClass());
						if (tmp instanceof CapturedTypeArgument) {
							casts.add(new IntroduceCast(vr, resolveCapturedTypeArgument(tmp)));
						}
						else casts.add(new IntroduceCast(vr, TypeKit.createTypeReference(ci, tmp, tr.getASTParent())));
					}
				}

				while (parent instanceof MethodReference || parent instanceof FieldReference) {
					Type ty = ci.getType(parent);
					if (!(ty instanceof ClassType)) {
						break;
					}
					if (!(ty instanceof TypeParameter)) {
//						System.out.println(((MethodReference)parent).getName() + " " + vs.getFullName() + " " + ty.getFullName());
						if (ty instanceof CapturedTypeArgument) {
							casts.add(new IntroduceCast((Expression)parent, resolveCapturedTypeArgument(ty)));
						}
						else casts.add(new IntroduceCast((Expression)parent, TypeKit.createTypeReference(ci, ty, parent)));
					}
					//TODO look at this
					else if (ty instanceof TypeParameter) {
						TypeParameterDeclaration tpd = (TypeParameterDeclaration)ci.getTypeDeclaration((ClassType)ty);
						if (tpd.getBoundCount() == 1) {
							if (ty instanceof CapturedTypeArgument) {
								casts.add(new IntroduceCast((Expression)parent, resolveCapturedTypeArgument(ty)));
							}
							else casts.add(new IntroduceCast((Expression)parent, TypeKit.createTypeReference(ci, ci.getType(tpd.getBounds().get(0)), parent)));
						}
						else if (tpd.getBoundCount() == 0) {
							casts.add(new IntroduceCast((Expression)parent, TypeKit.createTypeReference(getProgramFactory(), "Object")));
						}
						else if (tpd.getBoundCount() > 0) {
//							System.out.println(ty.getName() + " " + parent.toSource());
						}
					}
					parent = parent instanceof MethodReference ? ((MethodReference)parent).getReferenceSuffix() : ((FieldReference)parent).getReferenceSuffix();
//					System.out.println(parent instanceof MethodReference);
				} 
			}
		}
	}
	
	private TypeReference resolveCapturedTypeArgument(Type ty) {
		CapturedTypeArgument capTypeArg = (CapturedTypeArgument)ty;
		TypeReference tRef = null;
		Type tmp = null;
		ProgramFactory f = getProgramFactory();
		try {
			if (capTypeArg.getTypeArgument().getWildcardMode() == WildcardMode.None && capTypeArg.getTypeArgument() instanceof TypeArgumentDeclaration) {
				tRef = ((TypeArgumentDeclaration)capTypeArg.getTypeArgument()).getTypeReference();
			}
			else if (capTypeArg.getTypeArgument().getWildcardMode() == WildcardMode.Extends && capTypeArg.getTypeArgument() instanceof TypeArgumentDeclaration) {
				tRef = ((TypeArgumentDeclaration)capTypeArg.getTypeArgument()).getTypeReference();
			}
			//TODO what to do if Any
			else { //if (capTypeArg.getTypeArgument().getWildcardMode() == WildcardMode.Super || capTypeArg.getTypeArgument().getWildcardMode() == WildcardMode.Any) {
				return TypeKit.createTypeReference(getProgramFactory(), "Object");
			}
			tmp = getSourceInfo().getType(tRef);
//			if (tmp.getFullName().equals("edu.umd.cs.findbugs.gui2.HashList.E")) {
//				System.out.println();
//			}
			if (!(tmp instanceof TypeParameter)) {
				tRef = f.parseTypeReference(tmp.getFullName());
			}
			else {
				TypeParameter tp = (TypeParameter)tmp;
				if (tp.getBoundCount() > 0 && tp instanceof TypeParameterDeclaration) {
					for (int i = 0; i < tp.getBoundCount(); i++) {
						ASTList<TypeArgumentDeclaration> tadList = ((TypeParameterDeclaration)tp).getBoundTypeArguments(i);
						//TODO what if more than one bound
						if (tadList != null && tadList.size() > 0) {
							if (tadList.get(0).getWildcardMode() == WildcardMode.Extends) {
								tRef = ((TypeParameterDeclaration)tp).getBounds().get(0).deepClone();
							}
							else {
								tRef = TypeKit.createTypeReference(f, "Object");
							}
						}
					}
				}
				else {
					tRef = TypeKit.createTypeReference(f, "Object");
				}
			}
		}
		catch(ParserException e) {
			System.err.println("Parsing Exception");
		}
		return tRef;
	}

	@Override
	public ProblemReport analyze() {
//		System.out.println("ResolveGenerics: analyze()");
		
//		if (cu.getName().equals("FILE:/Users/tamarasteijger/Meine_Dateien/Schweden/Kurse/Master/RECODER/src/recoder/list/generic/ASTArrayList.java")) {
//			System.out.println();
//		}
//		parts = new ArrayList<TwoPassTransformation>();
		stuffToBeRemoved = new ArrayList<ProgramElement>();
//		trParts = new ArrayList<TwoPassTransformation>();
		casts = new ArrayList<IntroduceCast>();
		typeParamReferences = new ArrayList<TypeParamRefReplacement>();
		paramReplacements = new ArrayList<TypeParamRefReplacement>();
//		boxingCasts = new ArrayList<IntroduceBoxing>();
		CrossReferenceSourceInfo ci = getCrossReferenceSourceInfo();
		TreeWalker tw;
		for (CompilationUnit cu : cul) {
			tw = new TreeWalker(cu);
			while (tw.next()) {
				ProgramElement pe = tw.getProgramElement();
				NonTerminalProgramElement parent = pe.getASTParent();
				if (pe instanceof EnhancedFor) {
					System.err.println("Resolve Enhanced For Loops first!");
					return new TransformationNotApplicable(new EnhancedFor2For(getServiceConfiguration(),cul));
				}
				else if (pe instanceof TypeDeclaration && !(pe instanceof TypeParameterDeclaration)) {
					resolveSingleGenericType((TypeDeclaration)pe);
//					ResolveSingleGenericType p = new ResolveSingleGenericType(getServiceConfiguration(), (TypeDeclaration)pe, this);
//					if (p.analyze() != IDENTITY)
//						parts.add(p);
				} else if (pe instanceof MethodDeclaration) {
					resolveGenericMethod((MethodDeclaration)pe);
					resolveMethodReturnType((MethodDeclaration)pe);
//					ResolveGenericMethod p = new ResolveGenericMethod(getServiceConfiguration(), (MethodDeclaration)pe, this);
//					if (p.analyze() != IDENTITY)
//						parts.add(p);
				} else if (pe instanceof TypeReference) {
//					TwoPassTransformation p;
					TypeReference tr = (TypeReference)pe;
					if (parent instanceof MethodDeclaration) {
						MethodDeclaration md = (MethodDeclaration)parent;
						if (md.getTypeReference() != tr) continue; // argument, not return type
//						Type t = getSourceInfo().getType(tr);
//						CompilationUnit tcu = null;
//						if (t instanceof TypeDeclaration && !(t instanceof TypeParameterDeclaration)) {
//							/*CompilationUnit*/ tcu = UnitKit.getCompilationUnit((TypeDeclaration)t);
//							if (tcu == cu) continue;
//						}
	//					if (t != null) System.out.println("ResolveMethodReturnType I");
//						resolveMethodReturnType(md);
//						p = new ResolveMethodReturnType(getServiceConfiguration(), md, this);
					} else if (parent instanceof VariableDeclaration) { 
						Type t = getSourceInfo().getType(tr);
						if (t instanceof TypeDeclaration && !(t instanceof TypeParameterDeclaration)) {
							CompilationUnit tcu = UnitKit.getCompilationUnit((TypeDeclaration)t);
							if (tcu == cu) {
								continue;
							}
						}
						VariableDeclaration vd = (VariableDeclaration)parent;
						resolveSingleVariableDeclaration(vd);
//						p = new ResolveSingleVariableDeclaration(getServiceConfiguration(), vd, this);
					} else if (parent instanceof InheritanceSpecification) {
						InheritanceSpecification is = (InheritanceSpecification)parent;
//						TypeDeclaration supType = ci.getTypeDeclaration((ClassType)ci.getType(tr));
						ClassType supType = null;
//						ParameterizedType pType = null;
//						if (ci.getType(tr) instanceof ClassFile) supType = ci.getServiceConfiguration().getByteCodeInfo().getClassFile((ClassType)ci.getType(tr));
//						else if (ci.getType(tr) instanceof ParameterizedType) {
//							supType = ((ParameterizedType)ci.getType(tr)).getGenericType();
//							pType = (ParameterizedType)ci.getType(tr);
//						}
//						else supType = (ClassType)ci.getType(tr);
						supType = (ClassType)ci.getType(tr);
						if (supType == null) {
							continue;
						}
//						if (inheritedTypes.contains(supType)) {
//							continue;
//						}
//						inheritedTypes.add(supType);
						Type t = getSourceInfo().getType(tr);
						if (t instanceof TypeParameterDeclaration)
							continue; // will be taken care of by ResolveSingleGenericType
//						if (tr.getTypeArguments() == null) continue;
						// need to introduce type cast in every (inherited) method which
						// is not defined incurrent CU and has generic return type
						// TODO fields !!
						List<? extends Method> ml = supType.getAllMethods();
						if (tr.getTypeArguments() != null) {
							for (int i = 0; i < ml.size(); i++) {
								Method m = ml.get(i);
	//							if (m instanceof MethodInfo || (!(m instanceof ParameterizedMethod || m instanceof DummyGetClassMethod) && UnitKit.getCompilationUnit((MethodDeclaration)m) != cu)) {
								if (m instanceof ParameterizedMethod || ((m instanceof MethodInfo || (m instanceof MethodDeclaration && UnitKit.getCompilationUnit((MethodDeclaration)m) != cu))
										&& m.getReturnType() instanceof TypeParameter)) {
									resolveMethodReturnType(m);
								}
							}
						}
//						if (supType instanceof ParameterizedType) {
						
							TypeDeclaration tDecl = (TypeDeclaration)is.getASTParent();
							resolveParameterDeclaration(tDecl, supType);
							
//						}
						if (tr.getTypeArguments() != null) stuffToBeRemoved.addAll(tr.getTypeArguments());
						continue;
					} else if (parent instanceof MethodReference && parent.getASTParent() instanceof MethodReference) {
						// reference to static member
						Method m = getSourceInfo().getMethod((MethodReference)parent.getASTParent());
//						if (m instanceof MethodInfo || (!(m instanceof ParameterizedMethod || m instanceof DummyGetClassMethod) && UnitKit.getCompilationUnit((MethodDeclaration)m) != cu)) {
						if (m instanceof MethodInfo || (m instanceof MethodDeclaration && UnitKit.getCompilationUnit((MethodDeclaration)m) != cu)) {
	//						System.out.println("ResolveMethodReturnType III");
							resolveMethodReturnType(m);
//							p = new ResolveMethodReturnType(getServiceConfiguration(), m, this);
						} else continue;
					} else continue;
//					if (p.analyze() != IDENTITY)
//						trParts.add(p);
				} else if (pe instanceof New) {
					New n = (New)pe;
					if (n.getTypeReference().getTypeArguments() != null)
						stuffToBeRemoved.addAll(n.getTypeReference().getTypeArguments());
					if (n.getClassDeclaration() != null) {
						resolveParameterDeclaration(n.getClassDeclaration(), (ClassType)ci.getType(n));
					}
				} else if (pe instanceof NewArray) {
					NewArray n = (NewArray)pe;
					if (n.getTypeReference().getTypeArguments() != null)
						stuffToBeRemoved.addAll(n.getTypeReference().getTypeArguments());
				} else if (pe instanceof TypeCast) {
					TypeCast tc = (TypeCast)pe;
					if (tc.getTypeReference().getTypeArguments() != null)
						stuffToBeRemoved.addAll(tc.getTypeReference().getTypeArguments());
				} else if (pe instanceof Import) {
					ClassType ct = null;
					for (int i = 0; i < ((Import)pe).getTypeReferenceCount(); i++) {
						ct = (ClassType)ci.getType(((Import)pe).getTypeReferenceAt(i));
						if (ct instanceof ClassFile) {
							for (Method m : ct.getMethods()) {
								if (m.getReturnType() instanceof TypeParameter) {
									resolveMethodReturnType(m);
								}
							}
						}
					}
				} else if (pe instanceof MethodReference) {
					MethodReference mr = (MethodReference)pe;
					if (mr.getTypeArguments() != null && mr.getTypeArguments().size() > 0) {
						for (TypeArgumentDeclaration ta : mr.getTypeArguments()) {
							stuffToBeRemoved.add(ta);
						}
					}
					if (ci.getMethod(mr).getContainingClassType().getFullName().contains("java.lang.") && ci.getMethod(mr) instanceof ParameterizedMethod) {
						resolveMethodReturnType(ci.getMethod(mr));
					}
				}
			}
		}
//		if (parts.size() == 0 && trParts.size() == 0 && stuffToBeRemoved.size() == 0)
		if (casts.size() == 0 && stuffToBeRemoved.size() == 0)
			return setProblemReport(IDENTITY);
		return super.analyze();
	}
	
	private boolean doubleMethod(TypeDeclaration td, Method m) {
		SourceInfo ci = getSourceInfo();
		boolean res = false;
		for (Method m2 : td.getAllMethods()) {
			if (!m.equals(m2) && m.getName().equals(m2.getName()) && m.getSignature().size() == m2.getSignature().size() && !m2.isAbstract()) {
				for (int i = 0; i < m.getSignature().size(); i++) {
					if (m.getSignature().get(i) instanceof ClassType && m2.getSignature().get(i) instanceof ClassType &&
							ci.isSubtype((ClassType)m.getSignature().get(i), (ClassType)m2.getSignature().get(i))) {
						res = true;
						break;
					}
				}
			}
		}
		return res;
	}
	
	private void resolveParameterDeclaration(TypeDeclaration tDecl, ClassType supType) {
		List<? extends Method> ml = supType.getAllMethods();
		CrossReferenceSourceInfo ci = getCrossReferenceSourceInfo();
		for (int mDec = 0; mDec <  tDecl.getMethods().size(); mDec++) {
			Method mDecl = tDecl.getMethods().get(mDec);
			for (int i = ml.size() - 1; i >= 0; i--) {
				Method m = ml.get(i);

				if (mDecl instanceof MethodDeclaration && mDecl.getName().equals(m.getName()) && mDecl.getSignature().size() == m.getSignature().size()) { //) && sameSig) {
					if (doubleMethod(tDecl, mDecl)) break;
					ClassType containingClassType = null;
					List<Method> mList = MethodKit.getAllRedefinedMethods(mDecl);
					if (mList != null && mList.size() != 0) m = mList.get(0);
					if (m instanceof ParameterizedMethod) containingClassType = ((ParameterizedMethod)m).getGenericMethod().getContainingClassType();
					else if (m instanceof ErasedMethod) containingClassType = ((ErasedMethod)m).getGenericMethod().getContainingClassType();
					else containingClassType = m.getContainingClassType();
					if (containingClassType.getTypeParameters() == null || containingClassType.getTypeParameters().size() == 0) {
						break;
					}
					for (int k = 0; k < m.getSignature().size(); k++) {
						if ((m instanceof ParameterizedMethod  && ((ParameterizedMethod)m).getGenericMethod().getSignature().get(k) instanceof TypeParameter) ||
								(m instanceof ErasedMethod  && ((ErasedMethod)m).getGenericMethod().getSignature().get(k) instanceof TypeParameter)
								|| m.getSignature().get(k) instanceof TypeParameter) {
//											System.out.println(m.getSignature().get(k).getFullName());
//							if (pType.getTypeArgs() != null) {
								int indexTypeArg = - 1;
								for (int tp = 0; tp < containingClassType.getTypeParameters().size(); tp++) {
//									System.out.println(containingClassType.getTypeParameters().get(tp).getName());
									if (m instanceof ParameterizedMethod && containingClassType.getTypeParameters().get(tp).getName().equals(((ParameterizedMethod)m).getGenericMethod().getSignature().get(k).getName())) {
										indexTypeArg = tp;
										break;
									}
									else if (m instanceof ErasedMethod && containingClassType.getTypeParameters().get(tp).getName().equals(((ErasedMethod)m).getGenericMethod().getSignature().get(k).getName())) {
										indexTypeArg = tp;
										break;
									}
									else if (containingClassType.getTypeParameters().get(tp).getName().equals(m.getSignature().get(k).getName())) {
										indexTypeArg = tp;
										break;
									}
								}
								if (indexTypeArg == -1) continue;
//								System.out.println(((ParameterizedType)supType).getTypeArgs().get(indexTypeArg).getTypeName() + " " + pType.getGenericType().getTypeParameters().get(indexTypeArg).getBoundName(0));
								TypeReference typeArg = null;
								TypeReference param = ((MethodDeclaration)mDecl).getParameterDeclarationAt(k).getTypeReference();
								if (ci.getType(param) instanceof PrimitiveType) continue;
								if (containingClassType.getTypeParameters().get(indexTypeArg).getBoundCount() == 0 && param.getDimensions() == 0)		
									typeArg = TypeKit.createTypeReference(getProgramFactory(), "Object");
								else if (containingClassType.getTypeParameters().get(indexTypeArg).getBoundCount() == 0 && param.getDimensions() > 0) {
									typeArg = TypeKit.createTypeReference(getProgramFactory(), getNameInfo().createArrayType(getNameInfo().getJavaLangObject(), param.getDimensions()).getName());
								}
								else {
									typeArg = TypeKit.createTypeReference(getProgramFactory(), containingClassType.getTypeParameters().get(indexTypeArg).getBoundName(0));
								}
								typeArg = typeArg.deepClone();
								typeArg.setParent(((MethodDeclaration)mDecl).getParameterDeclarationAt(k).getTypeReference().getParent());
//								System.out.println(mDecl.getName() + " " + typeArg.getName() + " " + tDecl.getFullName() + " " + (param.getASTParent().getChildPositionCode(param) != -1));
								try {
									typeArg = getProgramFactory().parseTypeReference(ci.getType(typeArg).getFullName());
								}
								catch (ParserException e) {
									System.err.println("Parsing Exception");
								}
								paramReplacements.add(new TypeParamRefReplacement(param, typeArg));
//								System.out.println(mDecl.getName() + " " + typeArg.getReferencePrefix().toSource() + " " + typeArg.getName() + " " + tDecl.getFullName() + " " + (param.getASTParent().getChildPositionCode(param) != -1));
								List<VariableSpecification> varList = ((MethodDeclaration)mDecl).getParameterDeclarationAt(k).getVariables();
								for(Variable v : varList) {
									List<VariableReference> vrList = ci.getReferences(v);
									for(VariableReference vr : vrList) {
										if (isLeftHandSide(vr)) continue;
										Type ty = ci.getType(param);
										if (!(ty instanceof TypeParameter) && !(ty instanceof PrimitiveType)) {
//											System.out.println(((MethodReference)parent).getName() + " " + vs.getFullName() + " " + ty.getFullName());
											if (ty instanceof CapturedTypeArgument) {
												casts.add(new IntroduceCast(vr, resolveCapturedTypeArgument(ty)));
											}
											else casts.add(new IntroduceCast(vr, TypeKit.createTypeReference(ci, ty, vr)));
										}
										//TODO look at this
										else if (ty instanceof TypeParameter) {
											TypeParameterDeclaration tpd = (TypeParameterDeclaration)ci.getTypeDeclaration((ClassType)ty);
											if (tpd.getBoundCount() > 0) {
												if (ty instanceof CapturedTypeArgument) {
													casts.add(new IntroduceCast(vr, resolveCapturedTypeArgument(ty)));
												}
												else casts.add(new IntroduceCast(vr, TypeKit.createTypeReference(ci, ci.getType(tpd.getBounds().get(0)), vr)));
											}
											else if (tpd.getBoundCount() == 0) {
												casts.add(new IntroduceCast(vr, TypeKit.createTypeReference(getProgramFactory(), "Object")));
											}
										}
									}
								}
//							}
						}
					}
					break;
				}
			}
		}
	}

	@Override
	public void transform() {
		System.out.println("casts: " + casts.size() + " paramReplacements: " + paramReplacements.size() + " typeParamReferences: " + typeParamReferences.size() + " stuffToBeRemoved " + stuffToBeRemoved.size());
//		System.out.println("ResolveGenerics: transform()");
		super.transform();
//		System.out.println("Transforming Compilation Unit " + cu.getName());
		ProgramFactory f = getProgramFactory();
//		sortCasts(casts);
		sortCasts(casts);
//		removeAmbiguousCasts(casts);
//		for (int i = parts.size()-1; i >= 0; i--) {
//			parts.get(i).transform();
//		}
//		for (TwoPassTransformation tp : trParts) {
//			tp.transform();
//		}
		for (TypeParamRefReplacement t : paramReplacements) {
			MiscKit.unindent(t.replacement);
			if (t.typeParamRef.getASTParent().getChildPositionCode(t.typeParamRef) != -1)
				replace(t.typeParamRef, t.replacement);
			else {
				System.out.println("-1 " + t.typeParamRef.getName() + " " + t.replacement.getName());
			}
		}
		for (TypeParamRefReplacement t : typeParamReferences) {
			MiscKit.unindent(t.replacement);
			if (t.typeParamRef.getASTParent().getChildPositionCode(t.typeParamRef) != -1)
				replace(t.typeParamRef, t.replacement);
		}
		for (ProgramElement pe : stuffToBeRemoved) {
			if (pe.getASTParent().getIndexOfChild(pe) != -1)
				detach(pe);
		}
		for (IntroduceCast c : casts) {
			MiscKit.unindent(c.toBeCasted);
			if (c.toBeCasted.getASTParent().getIndexOfChild(c.toBeCasted) != -1 
				&&	!(c.toBeCasted.getASTParent() instanceof StatementContainer))
					replace(c.toBeCasted, f.createParenthesizedExpression(f.createTypeCast(c.toBeCasted.deepClone(), c.castedType)));
		}
	}
}
