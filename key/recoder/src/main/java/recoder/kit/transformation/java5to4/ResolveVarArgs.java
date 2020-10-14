/*
 * Created on 25.03.2006
 *
 * This file is part of the RECODER library and protected by the LGPL.
 * 
 */
package recoder.kit.transformation.java5to4;

import java.util.ArrayList;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.abstraction.ArrayType;
import recoder.abstraction.Constructor;
import recoder.abstraction.Method;
import recoder.abstraction.Type;
import recoder.convenience.TreeWalker;
import recoder.java.CompilationUnit;
import recoder.java.Expression;
import recoder.java.ProgramElement;
import recoder.java.declaration.ConstructorDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.ParameterDeclaration;
import recoder.java.expression.ArrayInitializer;
import recoder.java.expression.operator.NewArray;
import recoder.java.reference.ConstructorReference;
import recoder.java.reference.MemberReference;
import recoder.java.reference.MethodReference;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.kit.TypeKit;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/**
 * Replaces references to var arg methods and var arg methods itself to make it
 * java 1.4 compliant. Does not change redefined/redefining from different 
 * compilation units, so that an entire compilation unit list can be analyzed first
 * before being executed. Note that this means that, if used on a single compilation
 * unit, this transformation may lead to incompilable code.
 * @author Tobias Gutzmann
 * @since 0.80
 *
 */
public class ResolveVarArgs extends TwoPassTransformation {
	private List<CompilationUnit> cul;
	private List<MethodDeclaration> varArgMeths;
	private List<MemberReference> refs;
	private List<List<Type>> sigs;
	private List<Type> lastParamTypes;

	public ResolveVarArgs(CrossReferenceServiceConfiguration sc, CompilationUnit cu) {
		super(sc);
		cul = new ArrayList<CompilationUnit>();
		cul.add(cu);
	}
	
	public ResolveVarArgs(CrossReferenceServiceConfiguration sc, List<CompilationUnit> cul) {
		super(sc);
		this.cul = cul;
	}

	@Override
	public ProblemReport analyze() {
		varArgMeths = new ArrayList<MethodDeclaration>();
		refs = new ArrayList<MemberReference>();
		sigs = new ArrayList<List<Type>>();
		lastParamTypes = new ArrayList<Type>();
		TreeWalker tw;
		for (CompilationUnit cu : cul) {
			tw = new TreeWalker(cu);
			while (tw.next()) {
				ProgramElement pe = tw.getProgramElement();
				if (pe instanceof MethodDeclaration && !(pe instanceof ConstructorDeclaration)) {
					MethodDeclaration md = (MethodDeclaration)pe;
					if (md.isVarArgMethod()) {
						varArgMeths.add(md);
						lastParamTypes.add(getSourceInfo().getType(md.getParameterDeclarationAt(md.getParameterDeclarationCount()-1).getTypeReference()));
						List<MemberReference> rl = getCrossReferenceSourceInfo().getReferences(md);
						for (int i = 0, s = rl.size(); i < s; i++) {
							// if dimensions already match, don't add!!
							MethodReference toAdd = (MethodReference)rl.get(i);
							if (toAdd.getArguments() != null && toAdd.getArguments().size() == md.getParameterDeclarationCount()) {
								int idx = toAdd.getArguments().size()-1;
								Type tt = getSourceInfo().getType(toAdd.getArguments().get(idx)); 
								if (tt instanceof ArrayType && tt.equals(
										getSourceInfo().getType(md.getParameterDeclarationAt(idx).getVariableSpecification())))
									continue;
//								else if (tt instanceof ArrayType) {
//									System.out.println(md.getName() + " " + tt.getFullName() + " " + getSourceInfo().getType(md.getParameterDeclarationAt(idx).getVariableSpecification()).getFullName());
//								}
							}
							refs.add(toAdd);
							sigs.add(md.getSignature());
						}
					}
				}
				else if (pe instanceof ConstructorDeclaration) {
					ConstructorDeclaration cd = (ConstructorDeclaration)pe;
					if (cd.isVarArgMethod()) {
						varArgMeths.add(cd);
						lastParamTypes.add(getSourceInfo().getType(cd.getParameterDeclarationAt(cd.getParameterDeclarationCount()-1).getTypeReference()));
						List<ConstructorReference> cl = getCrossReferenceSourceInfo().getReferences(cd);
						for (int i = 0, s = cl.size(); i < s; i++) {
							// if dimensions already match, don't add!!
							ConstructorReference toAdd = cl.get(i);
							if (toAdd.getArguments() != null && toAdd.getArguments().size() == cd.getParameterDeclarationCount()) {
								int idx = toAdd.getArguments().size()-1;
								Type tt = getSourceInfo().getType(toAdd.getArguments().get(idx)); 
								if (tt instanceof ArrayType && tt.equals(
										getSourceInfo().getType(cd.getParameterDeclarationAt(idx).getVariableSpecification())))
									continue;
							}
							refs.add(toAdd);
							sigs.add(cd.getSignature());
						}
					}
				}
				else if (pe instanceof MethodReference) {
					MethodReference mr = (MethodReference)pe;
					Method m = getSourceInfo().getMethod(mr);
//					if (mr.getName().equals("getConstructor")) System.out.println("getConstructor I " + (m.isVarArgMethod())); 
					if (!(m instanceof MethodDeclaration) && m.isVarArgMethod()) {
//						System.err.println("Data uses VarArg Methods from the Java 5.0 Runtime Library -> Invocations of that method will be transformed but the code will need JRL 5.0 to run\n");
//						if (mr.getName().equals("getConstructor")) System.out.println("getConstructor II " + (mr.getArguments().size() == m.getSignature().size())); 
						if (mr.getArguments() != null && mr.getArguments().size() == m.getSignature().size()) {
							int idx = mr.getArguments().size() - 1;
							Type tt = getSourceInfo().getType(mr.getArguments().get(idx));
							if (!(tt instanceof ArrayType)) { // && tt.equals(getSourceInfo().getType(m.getSignature().get(idx))))) {
								refs.add(mr);
								sigs.add(m.getSignature());
							}
						}
						else if (mr.getArguments() != null) {
							refs.add(mr);
							sigs.add(m.getSignature());
						}					
					}
				}
				else if (pe instanceof ConstructorReference) {
					ConstructorReference n = (ConstructorReference)pe;
					Constructor c = getSourceInfo().getConstructor(n);
					if (!(c instanceof ConstructorDeclaration) && c.isVarArgMethod()) {
//						System.err.println("Data uses VarArg Constructor from the Java 5.0 Runtime Library -> Invocations of that method will be transformed but the code will need JRL 5.0 to run\n");
//						if (mr.getName().equals("getConstructor")) System.out.println("getConstructor II " + (mr.getArguments().size() == m.getSignature().size())); 
						if (n.getArguments() != null && n.getArguments().size() == c.getSignature().size()) {
							int idx = n.getArguments().size() - 1;
							Type tt = getSourceInfo().getType(n.getArguments().get(idx)); 
							if (!(tt instanceof ArrayType)) { // && tt.equals(getSourceInfo().getType(m.getSignature().get(idx))))) {
								refs.add(n);
								sigs.add(c.getSignature());
							}
						}
						else if (n.getArguments() != null) {
							refs.add(n);
							sigs.add(c.getSignature());
						}					
					}
				}
			}
		}
		return super.analyze();
	}

	@Override
	public void transform() {
		super.transform();
		ProgramFactory f = getProgramFactory();
		// TODO may not trigger update !!
		int idx = 0;
		System.out.println("refs: " + refs.size() + " varArgMeths: " + varArgMeths.size());
		for (MemberReference mr : refs) {
			List<Type> sig = sigs.get(idx++);
			int from = sig.size() - 1;
			int cnt = 0;
			ASTList<Expression> eml = new ASTArrayList<Expression>();
			if (mr instanceof MethodReference) {
				MethodReference methRef = (MethodReference)mr;
				cnt = methRef.getArguments() == null ? 0 : methRef.getArguments().size() - from;
				eml = new ASTArrayList<Expression>(cnt);
				for (int i = 0; i < cnt; i++) {
					eml.add(methRef.getArguments().get(from+i).deepClone());
				}
				ArrayInitializer ai = f.createArrayInitializer(eml);
				NewArray na = f.createNewArray(
					TypeKit.createTypeReference(f,
					sig.get(sig.size()-1)), 0, ai 
				);
				MethodReference repl = methRef.deepClone();
				while (cnt-- > 0)
					repl.getArguments().remove(repl.getArguments().size()-1);
				if (repl.getArguments() == null)
					repl.setArguments(new ASTArrayList<Expression>(0));
				repl.getArguments().add(na);
				repl.makeParentRoleValid();
				replace(mr, repl);
			}
			else if (mr instanceof ConstructorReference) {
				ConstructorReference cRef = (ConstructorReference)mr;
				cnt = cRef.getArguments() == null ? 0 : cRef.getArguments().size() - from;
				eml = new ASTArrayList<Expression>(cnt);
				for (int i = 0; i < cnt; i++) {
					eml.add(cRef.getArguments().get(from+i).deepClone());
				}
				ArrayInitializer ai = f.createArrayInitializer(eml);
				NewArray na = f.createNewArray(
					TypeKit.createTypeReference(f,
					sig.get(sig.size()-1)), 0, ai 
				);
				ConstructorReference repl = (ConstructorReference)cRef.deepClone();
				while (cnt-- > 0)
					repl.getArguments().remove(repl.getArguments().size()-1);
				if (repl.getArguments() == null)
					repl.setArguments(new ASTArrayList<Expression>(0));
				repl.getArguments().add(na);
				repl.makeParentRoleValid();
				replace(mr, repl);
			}
			
			
		}
		idx = 0;
		for (MethodDeclaration md : varArgMeths) {
			MethodDeclaration repl = md.deepClone();
			List<ParameterDeclaration> pds = md.getParameters();
			ParameterDeclaration pd = pds.get(pds.size()-1);
			ParameterDeclaration newpd = f.createParameterDeclaration(
					TypeKit.createTypeReference(f,
					getNameInfo().createArrayType(lastParamTypes.get(idx++))),
					pd.getVariableSpecification().getIdentifier().deepClone()
			);
			newpd.setVarArg(false);
			replace(repl.getParameterDeclarationAt(repl.getParameterDeclarationCount()-1), newpd);
			repl.makeParentRoleValid();
			replace(md, repl);
		}
	}
}
