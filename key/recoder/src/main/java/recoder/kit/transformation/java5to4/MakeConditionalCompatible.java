/*
 * Created on 17.03.2006
 *
 * This file is part of the RECODER library and protected by the LGPL.
 * 
 */
package recoder.kit.transformation.java5to4;

import java.util.ArrayList;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.abstraction.Field;
import recoder.abstraction.IntersectionType;
import recoder.abstraction.Method;
import recoder.abstraction.PrimitiveType;
import recoder.abstraction.Type;
import recoder.convenience.TreeWalker;
import recoder.java.CompilationUnit;
import recoder.java.Expression;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.expression.ParenthesizedExpression;
import recoder.java.expression.operator.Conditional;
import recoder.java.reference.FieldReference;
import recoder.java.reference.MethodReference;
import recoder.java.reference.TypeReference;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.kit.TypeKit;

/**
 * Deals with uses of the conditional(c-like trinary) operator which create intersection types.
 * @author Tobias Gutzmann
 *
 */
//* Conditionals which have conditionals in their subtree (i.e. (part of their) operands)
//* are not being considered. analyze() will report INCOMPLETE in such a case.
//* For complete effect, run again (and again(and again...)).
public class MakeConditionalCompatible extends TwoPassTransformation {

	private static class Item {
		Conditional c;
		Type t;
		Type p;
		Item(Conditional c, Type t) {
			this.c = c;
			this.t = t;
		}
		Item(Conditional c, Type t, Type p) {
			this.c = c;
			this.t = t;
			this.p = p;
		}
	}
	
	private NonTerminalProgramElement root;
	private List<CompilationUnit> cul;
	private List<Item> list;
	private List<Conditional> visited;
	
	/**
	 * @param sc
	 */
	public MakeConditionalCompatible(CrossReferenceServiceConfiguration sc, NonTerminalProgramElement root) {
		super(sc);
		this.root = root;
	}
	
	public MakeConditionalCompatible(CrossReferenceServiceConfiguration sc, List<CompilationUnit> cul) {
		super(sc);
		this.cul = cul;
	}

	private Type nestedConditionals(Conditional c, int deepth) {
		boolean inner = true;
		Type p = null;
		Type t = getSourceInfo().getType(c);
		Expression e1 = c.getExpressionAt(1);
		Expression e2 = c.getExpressionAt(2);
		Type t1 = getSourceInfo().getType(c.getExpressionAt(1)); 
		Type t2 = getSourceInfo().getType(c.getExpressionAt(2));
//		System.out.println("deepth: " + deepth + " t1: " + t1.getFullName() + " t2: " + t2.getFullName());
		if (e1 instanceof Conditional) {
			p = nestedConditionals((Conditional)e1, deepth + 1);
			inner = false;
		}
		if (e1 instanceof ParenthesizedExpression) {
			ParenthesizedExpression pe = (ParenthesizedExpression)e1;
			for (int i = 0; i < pe.getChildCount(); i++) {
				if (pe.getChildAt(i) instanceof Conditional) {
					p = nestedConditionals((Conditional)pe.getChildAt(i), deepth + 1);
					inner = false;
				}
			}
		}
		if (e2 instanceof Conditional) {
//			System.out.println("deepth: " + deepth + " e2 instanceof Conditional");
			p = nestedConditionals((Conditional)e2, deepth + 1);
			inner = false;
		}
		if (e2 instanceof ParenthesizedExpression) {
			ParenthesizedExpression pe = (ParenthesizedExpression)e2;
			for (int i = 0; i < pe.getChildCount(); i++) {
				if (pe.getChildAt(i) instanceof Conditional) {
					p = nestedConditionals((Conditional)pe.getChildAt(i), deepth + 1);
					inner = false;
				}
			}
		}
//		System.out.println("deepth: " + deepth);
//		System.out.println("deepth: " + deepth + " " + t1.getFullName() + " " + t2.getFullName());
		if (inner) p = t1;
		if (t instanceof IntersectionType || (t1 != t2 && 
				!(t1 instanceof PrimitiveType && t2 instanceof PrimitiveType) &&
				!(t1 == getNameInfo().getNullType()) && !(t2 == getNameInfo().getNullType()) &&
				!getSourceInfo().isWidening(t1, t2) && !getSourceInfo().isWidening(t2, t1)
		)) {
//			System.out.println("deepth: " + deepth + " To transform: " + t1.getFullName() + " " + t2.getFullName());
			NonTerminalProgramElement parent = c.getASTParent();
			Type target;
			if (parent instanceof MethodReference) {
				Method m = getSourceInfo().getMethod((MethodReference)parent);
				target = m.getContainingClassType(); 
			} else if (parent instanceof FieldReference){
				Field f = getSourceInfo().getField((FieldReference)parent);
				target = f.getContainingClassType();
			} else {
				target = getSourceInfo().getType(parent);
			} 
			// TODO any other special cases?
//			System.out.println(target.getClass() + " " + ((recoder.abstraction.ParameterizedType)target).getTypeArgs().get(0).getTypeName());
			list.add(new Item(c,target,p));
		}
		visited.add(c);
		return p;
	}
	
	@Override
	public ProblemReport analyze() {
		list = new ArrayList<Item>();
		visited = new ArrayList<Conditional>();
		setProblemReport(NO_PROBLEM);
		TreeWalker tw;
		if (cul != null) {
			for (CompilationUnit cu : cul) {
				root = cu;
				tw = new TreeWalker(root);
				while (tw.next()) {
					ProgramElement pe = tw.getProgramElement();
					if (pe instanceof Conditional) {
						Conditional c = (Conditional)pe;
						if (!visited.contains(c)) {
							nestedConditionals(c, 0);
						}
					}
				}
			}
		}
		else {
			tw = new TreeWalker(root);
			while (tw.next()) {
				ProgramElement pe = tw.getProgramElement();
				if (pe instanceof Conditional) {
					Conditional c = (Conditional)pe;
					if (!visited.contains(c)) {
						nestedConditionals(c, 0);
					}
				}
			}
		}
		if (list.isEmpty())
			return IDENTITY;
		return NO_PROBLEM;
	}

	@Override
	public void transform() {
		super.transform();
		ProgramFactory f = getProgramFactory();
		System.out.println("Conditionals to be transformed: " + list.size());
		for (Item i : list) {
			Expression e1 = i.c.getExpressionAt(1);
			Expression e2 = i.c.getExpressionAt(2);
			TypeReference tr1 = TypeKit.createTypeReference(f, i.t, true);
			TypeReference tr2 = TypeKit.createTypeReference(f, i.t, true);
			if (i.p instanceof recoder.abstraction.ParameterizedType) {
				TypeReference pr = TypeKit.createTypeReference(f, i.p, true);
				tr1.setTypeArguments(pr.getTypeArguments().deepClone());
				tr1.makeAllParentRolesValid();
				tr2.setTypeArguments(pr.getTypeArguments().deepClone());
				tr2.makeAllParentRolesValid();
			}
			replace(e1, f.createTypeCast(e1.deepClone(), tr1));
			replace(e2, f.createTypeCast(e2.deepClone(), tr2));
		}
	}
	
	

}
