//This file is part of KeY - Integrated Deductive Software Design 
//
//Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                      Technical University Darmstadt, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General 
//Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.MiscTools;

public class SLAbstractPlaceholderResolver extends SLExpressionResolver {
	 public SLAbstractPlaceholderResolver(JavaInfo javaInfo, 
   		  			SLResolverManager manager,
   		  			KeYJavaType specInClass) {
		 super(javaInfo, manager, specInClass);
	 }
	 
	 @Override
	 protected boolean canHandleReceiver(SLExpression receiver) {
	     return true;
	 }
	 
	 @Override
	 protected SLExpression doResolving(SLExpression receiver,
	                                    String name,
	                                    SLParameters parameters)
	                                throws SLTranslationException {
		 
		 if (name.equals("R") || name.equals("E") || name.equals("LS")) {
			 if (javaInfo.getServices().getNamespaces().functions().lookup(name) == null) {
								
				 Sort[] argsSorts = new Sort[parameters.getParameters().size()];
				 
				 ImmutableList<KeYJavaType> paramTypes = parameters.getSignature(services);
				 for (int i = 0; i<argsSorts.length; i++) {
					 argsSorts[i] = paramTypes.head().getSort();
					 paramTypes = paramTypes.tail();
				 }
				 
				 Function f = new Function(new Name(name), Sort.FORMULA, argsSorts);
				 javaInfo.getServices().getNamespaces().functions().add(f);
				 
				 Term[] arguments = new Term[parameters.getParameters().size()];
				 
				 ImmutableList<SLExpression> argumentsAsSLExp = parameters.getParameters();
				 for (int i = 0; i<arguments.length; i++) {
					 arguments[i] = argumentsAsSLExp.head().getTerm();
					 argumentsAsSLExp = argumentsAsSLExp.tail();
				 }
				 return null;
				 //services.getTypeConverter().getHeapLDT().getHeap().getKeYJavaType().getSort();
				 //return new SLExpression(TB.func(f, arguments));
				 //, services.getTypeConverter().getHeapLDT().getHeap()
			 } else {
				 return null;
			 }
			 
		 } else 
			 return null;
		 
	 }
}

