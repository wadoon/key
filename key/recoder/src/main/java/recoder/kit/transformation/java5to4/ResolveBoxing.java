/**
 * This file is part of the RECODER library and protected by the LGPL.
 */
package recoder.kit.transformation.java5to4;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.abstraction.ArrayType;
import recoder.abstraction.ClassType;
import recoder.abstraction.Constructor;
import recoder.abstraction.Method;
import recoder.abstraction.NullType;
import recoder.abstraction.PrimitiveType;
import recoder.abstraction.Type;
import recoder.convenience.TreeWalker;
import recoder.java.CompilationUnit;
import recoder.java.Expression;
import recoder.java.Identifier;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.declaration.VariableSpecification;
import recoder.java.expression.ArrayInitializer;
import recoder.java.expression.Assignment;
import recoder.java.expression.Operator;
import recoder.java.expression.operator.BinaryAnd;
import recoder.java.expression.operator.BinaryNot;
import recoder.java.expression.operator.BinaryOr;
import recoder.java.expression.operator.BinaryXOr;
import recoder.java.expression.operator.Conditional;
import recoder.java.expression.operator.Equals;
import recoder.java.expression.operator.NewArray;
import recoder.java.expression.operator.NotEquals;
import recoder.java.expression.operator.Plus;
import recoder.java.reference.ArrayReference;
import recoder.java.reference.ConstructorReference;
import recoder.java.reference.MethodReference;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.TypeReference;
import recoder.java.statement.Assert;
import recoder.java.statement.If;
import recoder.java.statement.Return;
import recoder.java.statement.Switch;
import recoder.kit.MiscKit;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.list.generic.ASTArrayList;
import recoder.service.NameInfo;
import recoder.service.SourceInfo;

/**
 * traverses a (sub)tree and replaces (un-)boxing 
 * conversions with explicit conversions.
 * 
 * @author Tobias Gutzmann
 * @since 0.80
 *
 */
public class ResolveBoxing extends TwoPassTransformation {
	
	private NonTerminalProgramElement root;
	private List<CompilationUnit> cul;
	private Map<Expression, ClassType> toUnbox = new HashMap<Expression, ClassType>();
	private Map<Expression, PrimitiveType> toBox = new HashMap<Expression, PrimitiveType>();
	private List<Expression> list = new ArrayList<Expression>();
	private List<Expression> remove = new ArrayList<Expression>();
	
	/**
	 * @param sc
	 * @param root
	 */
	public ResolveBoxing(CrossReferenceServiceConfiguration sc, NonTerminalProgramElement root) {
		super(sc);
		this.root = root;
	}
	
	public ResolveBoxing(CrossReferenceServiceConfiguration sc, List<CompilationUnit> cul) {
		super(sc);
		this.cul = cul;
	}
	
	private void traverse(TreeWalker tw) {
		SourceInfo si = getServiceConfiguration().getSourceInfo();
		while (tw.next()) {
			ProgramElement pe = tw.getProgramElement();
			if (pe instanceof Expression) { // && !(pe instanceof recoder.java.expression.operator.TypeCast)) {
				NonTerminalProgramElement parent = pe.getASTParent();
				Expression e = (Expression)pe;
				Type t = si.getType(e);
				Type tt = null; // target type
				if (parent instanceof MethodReference) {
//					System.out.println("parent instanceof MethodReference");
					// find out if boxing has been used
					MethodReference mr = (MethodReference)parent;
					Method m = si.getMethod(mr);
					if (mr.getArguments() != null) {
						int idx = mr.getArguments().indexOf(e);
						if (idx != -1 && idx < m.getSignature().size() && !m.isVarArgMethod())
							tt = m.getSignature().get(idx);
						else if (idx != -1 && m.isVarArgMethod()) {
							if (idx < m.getSignature().size() - 1) tt = m.getSignature().get(idx);
							else tt = ((ArrayType)m.getSignature().get(m.getSignature().size() - 1)).getBaseType();
						}
						
						// otherwise, expression is not used as an argument
						// but e.g. as a reference prefix 
					}
				} else if (parent instanceof ConstructorReference) {
					ConstructorReference n = (ConstructorReference)parent;
					Constructor c = si.getConstructor(n);
					if (n.getArguments() != null) {
						int idx = n.getArguments().indexOf(e);
						if (idx != -1 && idx < c.getSignature().size() && !c.isVarArgMethod())
							tt = c.getSignature().get(idx);
						else if (idx != -1 && c.isVarArgMethod()) {
							if (idx < c.getSignature().size() - 1) tt = c.getSignature().get(idx);
							else tt = ((ArrayType)c.getSignature().get(c.getSignature().size() - 1)).getBaseType();
						}
					}
				} else if (parent instanceof ArrayInitializer && !(pe instanceof ArrayInitializer)) {
					ArrayInitializer ai =(ArrayInitializer)parent;
					if (ai.getArguments() != null) {
						int idx = ai.getArguments().indexOf(e);
						if (idx != -1) {
							tt = ((ArrayType)si.getType(ai.getASTParent())).getBaseType();
							if (ai.getASTParent() instanceof ArrayInitializer) {
								tt = ((ArrayType)tt).getBaseType();
							}
						}
					}
				} else if (parent instanceof Operator && !(parent instanceof NewArray)) {
//					System.out.println("parent instanceof Operator");
					Operator op = (Operator)parent;
					if (op.getArity() == 2) {
						Type target = si.getType(op);
						if (target instanceof PrimitiveType && t instanceof ClassType
								&& !(t instanceof NullType) && !(t instanceof ArrayType)) {
							Expression ex = null;
							if (op.getExpressionAt(1).equals(e)) ex = op.getExpressionAt(0);
							else if (op.getExpressionAt(0).equals(e)) ex = op.getExpressionAt(1);
							if (!((op instanceof recoder.java.expression.operator.Equals ||
									op instanceof recoder.java.expression.operator.NotEquals) && ex != null &&
									si.getType(ex) instanceof ClassType && !(si.getType(ex) instanceof ArrayType))) {
								// unboxing needed
								tt = target;
							}
						}
						if (target instanceof ClassType && !target.getName().equals("String") && t instanceof PrimitiveType && !(target instanceof ArrayType)) { 
							tt = target;
						}
						if (!(op instanceof Assignment || op instanceof Equals || op instanceof NotEquals) && si.getType(op.getExpressionAt(0)) instanceof ClassType && si.getType(op.getExpressionAt(1)) instanceof ClassType) {
							if (!(op instanceof Plus && (si.getType(op.getExpressionAt(0)).getName().equals("String") || si.getType(op.getExpressionAt(1)).getName().equals("String")))) {
								Expression ex = op.getExpressionAt(0);
								list.add(ex);
								toUnbox.put(ex, (ClassType)si.getType(ex));
								ex = op.getExpressionAt(1);
								list.add(ex);
								toUnbox.put(ex, (ClassType)si.getType(ex));
							}
						}
					} else if (op.getArity() == 3) {
						/* if target is an intersection type, we always box for java 4 compatibility.
						 * But don't box first argument (condition)!
						 */ 
						if (op.getArguments().get(0) != e) {
							
							Type target = si.getType(op);
							//IntersectionTypes should be handled separatly
//							if (target instanceof IntersectionType) {
//								toBox.add(e);
//								list.add(e);
//							}
							/* in case it's not an intersection, but just a "most common" type:
							 /* example: (true ? "hello, world" : 5).getClass(); */
							if (t instanceof PrimitiveType && target instanceof ClassType && !(target instanceof ArrayType)) {
								toBox.put(e, (PrimitiveType)t);
								list.add(e);
							}
							else if (t instanceof ClassType && target instanceof PrimitiveType && !(t instanceof ArrayType)) {
								toUnbox.put(e, (ClassType)t);
								list.add(e);
							}
						}
							
					}
					else if (op.getArity() == 1 && !(op instanceof recoder.java.expression.operator.Instanceof ||
							op instanceof recoder.java.expression.operator.TypeCast ||
							op instanceof recoder.java.expression.ParenthesizedExpression)) {
						if (si.getType(e) instanceof ClassType && !(si.getType(e) instanceof ArrayType)) {
							t = si.getType(e);
							toUnbox.put(e, (ClassType)si.getType(e));
							list.add(e);
						}
					}
					else if (op instanceof recoder.java.expression.operator.TypeCast) {
						if (si.getType(op) instanceof ClassType && !(si.getType(op) instanceof ArrayType) && t instanceof PrimitiveType) {
							remove.add(e);
							list.add(e);
							toBox.put(e, (PrimitiveType)si.getType(e));
						}
						if (si.getType(op) instanceof PrimitiveType && t instanceof ClassType && !(t instanceof ArrayType)) {
							list.add(e);
							NameInfo ni = getServiceConfiguration().getNameInfo();
							if (!t.equals(ni.getJavaLangObject())) {
								toUnbox.put(e, (ClassType)t);
								remove.add(e);
							}
							else {
								tt = si.getType(op);
								if (tt == ni.getBooleanType()) {
									t = ni.getJavaLangBoolean();
								} else if (tt == ni.getByteType()) {
									t = ni.getJavaLangByte();
								} else if (tt == ni.getShortType()) {
									t = ni.getJavaLangShort();
								} else if (tt == ni.getCharType()) {
									t = ni.getJavaLangCharacter();
								} else if (tt == ni.getIntType()) {
									t = ni.getJavaLangInteger();
								} else if (tt == ni.getLongType()) {
									t = ni.getJavaLangLong();
								} else if (tt == ni.getFloatType()) {
									t = ni.getJavaLangFloat();
								} else if (tt == ni.getDoubleType()) {
									t = ni.getJavaLangDouble();
								}
								toUnbox.put(e, (ClassType)t);
							}
						}
					}
					/* else arity == 1 => nothing to do, because stuff like
					 * i++, where i is of type java.lang.Integer, is not allowed.
					 */
				} else if (parent instanceof VariableSpecification) {
					tt = ((VariableSpecification)parent).getType();
				} else if (parent instanceof Return) {
//					System.out.println("parent instanceof Return");
					tt = si.getType(MiscKit.getParentMemberDeclaration(parent));
				} else if (parent instanceof Switch) {
					if (t instanceof ClassType && !(t instanceof ArrayType) && !((ClassType)t).isEnumType()) {
//						System.out.println("parent instanceof Switch");
						toUnbox.put(e, (ClassType)t);
						list.add(e);
					}
				} else if (parent instanceof Assert) {
					//not needed, only condition needs to be checked but this will happen in section Operator
//					if (t instanceof ClassType) {
//						System.out.println("parent instanceof Assert " + parent.getChildCount());
//						toUnbox.add(e);
//						list.add(e);
//					}
				} else if (parent instanceof ArrayReference || parent instanceof NewArray) {
//					System.out.println(parent.toSource());
					if (t instanceof ClassType && !(t instanceof ArrayType)) {
//						System.out.println("parent instanceof ArrayReference");
						toUnbox.put(e, (ClassType)t);
						list.add(e);
					}
				} else if (parent instanceof If) {
					If ifSt = (If)parent;
					if (e.equals(ifSt.getExpression())) {
						if (t instanceof ClassType) {
							toUnbox.put(e, (ClassType)t);
							list.add(e);
						}
					}
				} else if (parent instanceof Conditional) {
					Conditional condSt = (Conditional)parent;
					if (e.equals(condSt.getExpressionAt(0))) {
						if (t instanceof ClassType) {
							toUnbox.put(e, (ClassType)t);
							list.add(e);
						}
					}
				}
				if (tt != null) {
					if (tt instanceof ClassType && t instanceof PrimitiveType && !(tt instanceof ArrayType)) {
//						System.out.println("Boxing");
						toBox.put(e, (PrimitiveType)t);
						list.add(e);
					}
					else if (tt instanceof PrimitiveType && t instanceof ClassType && !(t instanceof ArrayType)) {
//						System.out.println("Unboxing");
						toUnbox.put(e, (ClassType)t);
						list.add(e);
					}
					else if (tt instanceof ClassType && t instanceof ClassType && !(tt instanceof ArrayType) && !(t instanceof ArrayType)) {
						if (e instanceof BinaryOr || e instanceof BinaryNot || e instanceof BinaryXOr || e instanceof BinaryAnd) {
							Operator op = (Operator)e;
							Type t1 = si.getType(op.getExpressionAt(0));
							Type t2 = si.getType(op.getExpressionAt(1));
							if (t1 instanceof ClassType && !(t1 instanceof ArrayType) && t2 instanceof ClassType && !(t2 instanceof ArrayType)) {
//								System.out.println("tuuut " + op.toSource() + " " + t.getFullName());
								NameInfo ni = getServiceConfiguration().getNameInfo();
								list.add(e);
								if (t == ni.getJavaLangBoolean()) {
									toBox.put(e, ni.getBooleanType());
								} else if (t == ni.getJavaLangByte()) {
									toBox.put(e, ni.getByteType());
								} else if (t == ni.getJavaLangShort()) {
									toBox.put(e, ni.getShortType());
								} else if (t == ni.getJavaLangCharacter()) {
									toBox.put(e, ni.getCharType());
								} else if (t == ni.getJavaLangInteger()) {
									toBox.put(e, ni.getIntType());
								} else if (t == ni.getJavaLangLong()) {
									toBox.put(e, ni.getLongType());
								} else if (t == ni.getJavaLangFloat()) {
									toBox.put(e, ni.getFloatType());
								} else if (t == ni.getJavaLangDouble()) {
									toBox.put(e, ni.getDoubleType());
								} else throw new Error("cannot unbox type " + t.getFullName() + " ("+t.getClass()+")\n"
										+ e.getClass() + " " + e.getASTParent().getClass() + "\n"
										+ si.getType(e) + " " + si.getType(e.getASTParent()));
							}
						}
					}
				}
			}
		}
	}

	@Override
	public ProblemReport analyze() {
		TreeWalker tw;
		if (cul != null) {
			for (CompilationUnit cu : cul) {
				tw = new TreeWalker(cu);
				traverse(tw);
			}
		}
		else {
			tw= new TreeWalker(root);
			traverse(tw);
		}

		return super.analyze();
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
	
	private void sortExpressions(List<Expression> ex) {
		boolean changed = true;
		Expression ex1,ex2,tmp;
		NonTerminalProgramElement ntpe = null;
		while (changed) {
			changed = false;
			for (int i = 0; i < ex.size() - 1; i++) {
				for (int j = i + 1; j < ex.size(); j++) {
					ex1 = ex.get(i);
					ex2 = ex.get(j);
					if (ex1 instanceof NonTerminalProgramElement) {
						ntpe = (NonTerminalProgramElement) ex1;
						if (isChild(ntpe,ex2)) {
							tmp = ex.get(i);
							ex.set(i, ex2);
							ex.set(j, tmp);
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
//		for (int i = 0; i < list.size(); i++) {
//			if (list.lastIndexOf(list.get(i)) != i) {
//				list.remove(i);
//			}
//		}
		sortExpressions(list);
		ProgramFactory f = getProgramFactory();
		SourceInfo si = getServiceConfiguration().getSourceInfo();
		NameInfo ni = getServiceConfiguration().getNameInfo();
		System.out.println("toBox: " + toBox.size() + " toUnbox: " + toUnbox.size() + " remove: " + remove.size() + " list " + list.size());
		MethodReference replacement;
		for (Expression e : list) {
			replacement = null;
			if (toUnbox.containsKey(e)) {
				Identifier id;
				ClassType t = toUnbox.get(e);
				if (t == ni.getJavaLangBoolean()) {
					id = f.createIdentifier("booleanValue");
				} else if (t == ni.getJavaLangByte()) {
					id = f.createIdentifier("byteValue");
				} else if (t == ni.getJavaLangShort()) {
					id = f.createIdentifier("shortValue");
				} else if (t == ni.getJavaLangCharacter()) {
					id = f.createIdentifier("charValue");
				} else if (t == ni.getJavaLangInteger()) {
					id = f.createIdentifier("intValue");
				} else if (t == ni.getJavaLangLong()) {
					id = f.createIdentifier("longValue");
				} else if (t == ni.getJavaLangFloat()) {
					id = f.createIdentifier("floatValue");
				} else if (t == ni.getJavaLangDouble()) {
					id = f.createIdentifier("doubleValue");
				} else throw new Error("cannot unbox type " + t.getFullName() + " ("+t.getClass()+")\n"
						+ e.getClass() + " " + e.getASTParent().getClass() + "\n"
						+ si.getType(e) + " " + si.getType(e.getASTParent()) + " " + e.getASTParent().toSource());
				ReferencePrefix rp;
				if (e instanceof ReferencePrefix)
					rp = (ReferencePrefix)e.deepClone();
				else 
					rp = f.createParenthesizedExpression(e.deepClone());
				replacement = f.createMethodReference(rp, id);
//				if (!remove.contains(e)) replace(e, replacement);
				if (e.getASTParent().getChildPositionCode(e) == -1) {
//					System.out.println("e " + e.toSource() + " " + remove.contains(e) + " " + toBox.containsKey(e) + " " + toUnbox.containsKey(e));
//					System.out.println("parent " + e.getASTParent().toSource());
				} else
					if (!remove.contains(e)) replace(e, replacement);
//					replace(e, replacement);
			}
			if (toBox.containsKey(e)) {
				PrimitiveType t = toBox.get(e);
				Expression tmp;
				if (replacement != null) {
					tmp = (Expression)replacement.getASTParent();
				} else tmp = e;
				Identifier id;
//				PrimitiveType t = toBox2.get(e);
				if (t == ni.getBooleanType()) {
					id = f.createIdentifier("Boolean");
				} else if (t == ni.getByteType()) {
					id = f.createIdentifier("Byte");
				} else if (t == ni.getShortType()) {
					id = f.createIdentifier("Short");
				} else if (t == ni.getCharType()) {
					id = f.createIdentifier("Character");
				} else if (t == ni.getIntType()) {
					id = f.createIdentifier("Integer");
				} else if (t == ni.getLongType()) {
					id = f.createIdentifier("Long");
				} else if (t == ni.getFloatType()) {
					id = f.createIdentifier("Float");
				} else if (t == ni.getDoubleType()) {
					id = f.createIdentifier("Double");
				} else {
					System.out.println("cannot box: " + si.getType(tmp) + " " + t);
					throw new Error();
				}
				TypeReference tr = f.createTypeReference(id);
				replacement = f.createMethodReference(tr, 
						f.createIdentifier("valueOf"),
						new ASTArrayList<Expression>(
								tmp.deepClone()
						)
				);
				if (!remove.contains(e)) replace(tmp, replacement);
//				replace(tmp, replacement);
			}
			if (remove.contains(e) && replacement != null) {
//				System.out.println(UnitKit.getCompilationUnit(e).getName());
				replace(e.getASTParent(), replacement);
			}
		}
	}
}
