/**
 * 
 */
package recoder.service;

import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ModelException;
import recoder.abstraction.ArrayType;
import recoder.abstraction.ClassType;
import recoder.abstraction.Method;
import recoder.abstraction.ParameterizedType;
import recoder.abstraction.PrimitiveType;
import recoder.abstraction.Type;
import recoder.abstraction.TypeArgument.CapturedTypeArgument;
import recoder.convenience.Format;
import recoder.convenience.Formats;
import recoder.convenience.TreeWalker;
import recoder.java.CompilationUnit;
import recoder.java.Expression;
import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.declaration.ClassInitializer;
import recoder.java.declaration.FieldDeclaration;
import recoder.java.declaration.LocalVariableDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.expression.operator.CopyAssignment;
import recoder.java.reference.MethodReference;
import recoder.java.reference.SuperReference;
import recoder.java.reference.TypeReference;
import recoder.java.statement.EnhancedFor;
import recoder.java.statement.If;
import recoder.kit.UnitKit;

/**
 * Currently, this class is a "stand alone" checker, not incorporated into
 * the other services, and must be called from "the outside". Future versions
 * of this class may work differently, i.e., be integrated into the model
 * update process.
 * This class is WORK IN PROGRESS and doesn't at all cover all the semantics
 * checks from the Java Language Specification yet! 
 * @since 0.92 
 * TODO: may need to be reworked to be better integrated into services. 
 * @author Tobias Gutzmann
 * 
 */
public class SemanticsChecker {
	private final CrossReferenceServiceConfiguration crsc;
	private final SourceInfo si;
	private final NameInfo ni;
	private boolean java5allowed;
	private ErrorHandler errorHandler;
	private final SemanticsCheckerVisitor checker = new SemanticsCheckerVisitor();
	
	/**
	 * 
	 */
	public SemanticsChecker(CrossReferenceServiceConfiguration crsc) {
		this.crsc = crsc;
		si = crsc.getSourceInfo();
		ni = crsc.getNameInfo();
	}
	
	public void checkAllCompilationUnits() throws ModelException {
		for (CompilationUnit cu : crsc.getSourceFileRepository().getCompilationUnits()) {
			check(cu);
		}
	}
	
	public void check(CompilationUnit cu) throws ModelException {
		// TODO does not support setting compatibility to different versions yet!!
		java5allowed = crsc.getProjectSettings().java5Allowed();

		errorHandler = crsc.getProjectSettings().getErrorHandler();
		
		// check each single element in the tree:
		TreeWalker tw = new TreeWalker(cu);
		while (tw.next()) {
			tw.getProgramElement().accept(checker);
		}
	}

	/**
	 * The SourceVisitor carrying the actual semantics
	 * @author Tobias Gutzmann
	 */
	private class SemanticsCheckerVisitor extends SourceVisitor {
		@Override
		public void visitIf(If x) {
	    	Type exprType = si.getType(x.getExpression()); 
	    	if (!(exprType == ni.getBooleanType() || 
	    			(java5allowed && exprType == ni.getJavaLangBoolean()))) {
	    		errorHandler.reportError(
	    				new TypingException(x.getExpression()));
	    	}
		}
		
		@Override
		public void visitEnhancedFor(EnhancedFor ef) {
			Type lhsType = 
				si.getType(((LocalVariableDeclaration)ef.getInitializers().get(0)).getTypeReference());
			Type rhsType =
				si.getType(ef.getGuard());
			if (rhsType instanceof ArrayType) {
				if (si.isWidening(((ArrayType) rhsType).getBaseType(), lhsType))
					return; // ok!
			} else {
				// Is it an Iterable type on the right?
				List<ClassType> allSupers = si.getAllSupertypes((ClassType)rhsType);
				// find the supertype "Iterable"
				ClassType iterableType = null;
				for(ClassType ct: allSupers) {
					if (ct.getFullName().equals("java.lang.Iterable")) {
						iterableType = ct;
						break;
					}
				}
				// first of all, rhs MUST have java.lang.Iterable as supertype!
				if (iterableType != null) {
					if (lhsType == ni.getJavaLangObject())
						return; // ok. the for loop has java.lang.Object as lhs, which is always possible to assign
					// check if type arguments match
					if (iterableType instanceof ParameterizedType) {
						ClassType rhsTypeArg = ((DefaultSourceInfo)si).getBaseType(((ParameterizedType)iterableType).getTypeArgs().get(0));
						if (si.isWidening(lhsType,rhsTypeArg))
							return; // ok!
					}
				}
			}
			// lhs and rhs don't match, or rhs is not even an instance of java.lang.Iterable -> error!
			System.out.println(UnitKit.getCompilationUnit(ef).getName());
			errorHandler.reportError(
					new TypingException("lhs does not match rhs - " + lhsType.getFullSignature() + " : " + rhsType.getFullSignature(), ef.getGuard()));
		}
		
		
		@Override
		public void visitCopyAssignment(CopyAssignment ca) {
			Type lhs = si.getType(ca.getChildAt(0));
	    	Type rhs = si.getType(ca.getChildAt(1));
			if (lhs instanceof PrimitiveType && !(rhs instanceof PrimitiveType))
				rhs = si.getUnboxedType((ClassType)rhs);
			else if (rhs instanceof PrimitiveType && !(lhs instanceof PrimitiveType))
				rhs = si.getBoxedType((PrimitiveType)rhs);
			else if (rhs instanceof CapturedTypeArgument)
				rhs = ((DefaultSourceInfo)si).getBaseType(((CapturedTypeArgument)rhs).getTypeArgument());
	    	if (!si.isWidening(
	    			rhs, lhs)) {
	    		if (rhs instanceof PrimitiveType &&
	    			si.getServiceConfiguration().getConstantEvaluator().isCompileTimeConstant((Expression)ca.getChildAt(1))) {
	    			// TODO needs extra check...
	    			// byte b = 5; <- valid code, while
	    			// void foo(byte b) { foo(5);} <- isn't
	    			return;
	    		}
	    		// TODO better error report...
	    		errorHandler.reportError(new ModelException("Invalid assignment"));
	    	}
		}
		
		@Override
		public void visitMethodReference(MethodReference mr) {
			Method m = si.getMethod(mr);
			String msg;
			if ((msg = isAppropriate(m, mr)) != null) {
				errorHandler.reportError(
						new UnresolvedReferenceException(
                        		Format.toString(
                                "Inappropriate method access: " + msg + " at " + Formats.ELEMENT_LONG, mr), mr));

			}
		}
		
		/** 
		 * helper method for visitMethodReference
		 * UNTESTED AND INCOMPLETE !!!
		 */
	    private final String isAppropriate(Method m, MethodReference mr) {
	        // follows JLS §15.12.3
	        // TODO Ya Liu ...
	        if (mr.getReferencePrefix() == null) {
	            return m.isStatic() || !occursInStaticContext(mr) ? null : "method invocation to non-static method occurs in static context (a)"; 
	        }
	        if (mr.getReferencePrefix() instanceof TypeReference && !m.isStatic()) {
	        	// static access to a nun-static member
	        	return "Static access to a non-static member";
	        }
	        if (mr.getTypeReferenceCount() == 1) {
	            // access path is static, so method must be static, too
	        	// TODO this may also be a reference to an outer type, so this check is removed for now!
	            //return m.isStatic() ? null : "method invocation to non-static method occurs in static context (b)";
	        	return null;
	        }
	        if (mr.getReferencePrefix() instanceof SuperReference) {
	            SuperReference sr = (SuperReference)mr.getReferencePrefix();
	            if (m.isAbstract()) {
	            	//System.out.println(m.getContainingClassType().getFullName());
	            	//return "cannot access super method because it is abstract";
	            	// TODO this one may trigger a bug if an interfaces re-declares methods from java.lang.Object,
	            	// e.g. public object clone() 
	            }
	            if (occursInStaticContext(mr)) return "method invocation to non-static method occurs in static context (c)";
	            if (sr.getReferencePrefix() != null && (sr.getReferencePrefix() instanceof TypeReference)) {
	                // TODO
	                /* 
	                 * "Let C be the class denoted by ClassName. If the invocation
	                 *  is not directly enclosed by C or an inner class of C, then
	                 *  a compile-time error occurs"
	                 */
	            }
	            return null;
	        }
	        if (mr.getReferenceSuffix() != null && m.getReturnType() == null)
	            return "void method must not have a reference suffix";
	        return null;
	    }
	    
	    // helper method for visitMethodReference
	    private final boolean occursInStaticContext(MethodReference mr) {
	    	ProgramElement pe = mr;
	        while (pe != null) {
	            if (pe instanceof ClassInitializer)
	                return ((ClassInitializer)pe).isStatic();
	            if (pe instanceof MethodDeclaration)
	                return ((MethodDeclaration)pe).isStatic();
	            if (pe instanceof FieldDeclaration)
	            	return ((FieldDeclaration)pe).isStatic();
	            pe = pe.getASTParent();
	        }
	        // this *hopefully* only happens if parent links aren't set properly
	        throw new RuntimeException("cannot determine if MethodReference " + 
	        		Format.toString(pe) + " occurs in static context; check parent links!");
	    }
	}
}
